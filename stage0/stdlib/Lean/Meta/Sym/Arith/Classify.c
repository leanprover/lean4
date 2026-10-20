// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Classify
// Imports: public import Lean.Meta.Sym.Arith.Insts import Lean.Meta.Sym.SynthInstance import Lean.Meta.Sym.Canon import Lean.Meta.DecLevel import Init.Grind.Ring
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getArithState___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_arithExt;
lean_object* l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getCharInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_registerInstance___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
extern lean_object* l_Lean_Nat_mkType;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
extern lean_object* l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
lean_object* l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "OfCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ofCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 56, 247, 159, 186, 83, 86, 251)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(36, 61, 219, 203, 190, 113, 236, 200)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toCommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(134, 95, 181, 253, 18, 104, 213, 131)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "CommSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "NatModule"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 171, 186, 15, 174, 251, 179)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toNatModule"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(156, 107, 255, 119, 73, 35, 26, 237)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__23_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__31_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__33_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__35_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__37_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__39_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__41_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__43_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__45_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__48_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__50_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__52_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__54_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__56_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__58_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__59_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "PowIdentity available: false"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "NoNatZeroDivisors available: "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "instNoNatZeroDivisorsQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__69_value),LEAN_SCALAR_PTR_LITERAL(221, 130, 167, 21, 145, 237, 132, 218)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "instIsCharPQOfAddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__71_value),LEAN_SCALAR_PTR_LITERAL(194, 21, 126, 159, 192, 171, 59, 180)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__73_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "AddRightCancel"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__75_value),LEAN_SCALAR_PTR_LITERAL(33, 101, 175, 31, 110, 234, 168, 33)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "new ring: "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "PowIdentity available: "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Q"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__68_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 238, 182, 216, 107, 45, 243, 168)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__17_value),LEAN_SCALAR_PTR_LITERAL(69, 110, 106, 77, 169, 45, 119, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(134, 3, 13, 60, 96, 160, 201, 59)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unexpected failure initializing ring"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OrderedRing"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 123, 155, 51, 122, 17, 247, 247)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0(lean_object* v___x_1_, lean_object* v_s_2_){
_start:
{
lean_object* v_exp_3_; lean_object* v_rings_4_; lean_object* v_semirings_5_; lean_object* v_ncRings_6_; lean_object* v_ncSemirings_7_; lean_object* v_typeClassify_8_; lean_object* v_orders_9_; lean_object* v_typeOrderClassify_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
v_exp_3_ = lean_ctor_get(v_s_2_, 0);
v_rings_4_ = lean_ctor_get(v_s_2_, 1);
v_semirings_5_ = lean_ctor_get(v_s_2_, 2);
v_ncRings_6_ = lean_ctor_get(v_s_2_, 3);
v_ncSemirings_7_ = lean_ctor_get(v_s_2_, 4);
v_typeClassify_8_ = lean_ctor_get(v_s_2_, 5);
v_orders_9_ = lean_ctor_get(v_s_2_, 6);
v_typeOrderClassify_10_ = lean_ctor_get(v_s_2_, 7);
v_isSharedCheck_18_ = !lean_is_exclusive(v_s_2_);
if (v_isSharedCheck_18_ == 0)
{
v___x_12_ = v_s_2_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_typeOrderClassify_10_);
lean_inc(v_orders_9_);
lean_inc(v_typeClassify_8_);
lean_inc(v_ncSemirings_7_);
lean_inc(v_ncRings_6_);
lean_inc(v_semirings_5_);
lean_inc(v_rings_4_);
lean_inc(v_exp_3_);
lean_dec(v_s_2_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_14_ = lean_array_push(v_rings_4_, v___x_1_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_exp_3_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_17_, 2, v_semirings_5_);
lean_ctor_set(v_reuseFailAlloc_17_, 3, v_ncRings_6_);
lean_ctor_set(v_reuseFailAlloc_17_, 4, v_ncSemirings_7_);
lean_ctor_set(v_reuseFailAlloc_17_, 5, v_typeClassify_8_);
lean_ctor_set(v_reuseFailAlloc_17_, 6, v_orders_9_);
lean_ctor_set(v_reuseFailAlloc_17_, 7, v_typeOrderClassify_10_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(lean_object* v___x_22_, lean_object* v_____do__lift_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_toCold_31_; lean_object* v_options_32_; uint8_t v_hasTrace_33_; 
v_toCold_31_ = lean_ctor_get(v___y_28_, 0);
v_options_32_ = lean_ctor_get(v_toCold_31_, 2);
v_hasTrace_33_ = lean_ctor_get_uint8(v_options_32_, sizeof(void*)*1);
if (v_hasTrace_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v___x_22_);
v___x_34_ = lean_box(v_hasTrace_33_);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; uint8_t v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_36_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1));
v___x_37_ = l_Lean_Name_append(v___x_36_, v___x_22_);
v___x_38_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_23_, v_options_32_, v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = lean_box(v___x_38_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___boxed(lean_object* v___x_41_, lean_object* v_____do__lift_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_41_, v_____do__lift_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec_ref(v_____do__lift_42_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(lean_object* v_msgData_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v_env_58_; uint8_t v___x_59_; lean_object* v_env_60_; lean_object* v___x_61_; lean_object* v_toCold_62_; lean_object* v_mctx_63_; lean_object* v_lctx_64_; lean_object* v_options_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_57_ = lean_st_ref_get(v___y_55_);
v_env_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc_ref(v_env_58_);
lean_dec(v___x_57_);
v___x_59_ = 0;
v_env_60_ = l_Lean_Environment_setRecordingDeps(v_env_58_, v___x_59_);
v___x_61_ = lean_st_ref_get(v___y_53_);
v_toCold_62_ = lean_ctor_get(v___y_54_, 0);
v_mctx_63_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_mctx_63_);
lean_dec(v___x_61_);
v_lctx_64_ = lean_ctor_get(v___y_52_, 2);
v_options_65_ = lean_ctor_get(v_toCold_62_, 2);
lean_inc_ref(v_options_65_);
lean_inc_ref(v_lctx_64_);
v___x_66_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_66_, 0, v_env_60_);
lean_ctor_set(v___x_66_, 1, v_mctx_63_);
lean_ctor_set(v___x_66_, 2, v_lctx_64_);
lean_ctor_set(v___x_66_, 3, v_options_65_);
v___x_67_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_msgData_51_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(v_msgData_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_75_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_76_; double v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_float_of_nat(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(lean_object* v_cls_81_, lean_object* v_msg_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_ref_88_; lean_object* v___x_89_; lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_135_; 
v_ref_88_ = lean_ctor_get(v___y_85_, 2);
v___x_89_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0_spec__0(v_msg_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_135_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_135_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_135_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v_traceState_95_; lean_object* v_env_96_; lean_object* v_nextMacroScope_97_; lean_object* v_ngen_98_; lean_object* v_auxDeclNGen_99_; lean_object* v_cache_100_; lean_object* v_recordedDeps_101_; lean_object* v_messages_102_; lean_object* v_infoState_103_; lean_object* v_snapshotTasks_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_134_; 
v___x_94_ = lean_st_ref_take(v___y_86_);
v_traceState_95_ = lean_ctor_get(v___x_94_, 4);
v_env_96_ = lean_ctor_get(v___x_94_, 0);
v_nextMacroScope_97_ = lean_ctor_get(v___x_94_, 1);
v_ngen_98_ = lean_ctor_get(v___x_94_, 2);
v_auxDeclNGen_99_ = lean_ctor_get(v___x_94_, 3);
v_cache_100_ = lean_ctor_get(v___x_94_, 5);
v_recordedDeps_101_ = lean_ctor_get(v___x_94_, 6);
v_messages_102_ = lean_ctor_get(v___x_94_, 7);
v_infoState_103_ = lean_ctor_get(v___x_94_, 8);
v_snapshotTasks_104_ = lean_ctor_get(v___x_94_, 9);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_134_ == 0)
{
v___x_106_ = v___x_94_;
v_isShared_107_ = v_isSharedCheck_134_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_snapshotTasks_104_);
lean_inc(v_infoState_103_);
lean_inc(v_messages_102_);
lean_inc(v_recordedDeps_101_);
lean_inc(v_cache_100_);
lean_inc(v_traceState_95_);
lean_inc(v_auxDeclNGen_99_);
lean_inc(v_ngen_98_);
lean_inc(v_nextMacroScope_97_);
lean_inc(v_env_96_);
lean_dec(v___x_94_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_134_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
uint64_t v_tid_108_; lean_object* v_traces_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_133_; 
v_tid_108_ = lean_ctor_get_uint64(v_traceState_95_, sizeof(void*)*1);
v_traces_109_ = lean_ctor_get(v_traceState_95_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_traceState_95_);
if (v_isSharedCheck_133_ == 0)
{
v___x_111_ = v_traceState_95_;
v_isShared_112_ = v_isSharedCheck_133_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_traces_109_);
lean_dec(v_traceState_95_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_133_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; double v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_box(0);
v___x_115_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__0);
v___x_116_ = 0;
v___x_117_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__1));
v___x_118_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_118_, 0, v_cls_81_);
lean_ctor_set(v___x_118_, 1, v___x_114_);
lean_ctor_set(v___x_118_, 2, v___x_117_);
lean_ctor_set_float(v___x_118_, sizeof(void*)*3, v___x_115_);
lean_ctor_set_float(v___x_118_, sizeof(void*)*3 + 8, v___x_115_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*3 + 16, v___x_116_);
v___x_119_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___closed__2));
v___x_120_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v_a_90_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
lean_inc(v_ref_88_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_ref_88_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Lean_PersistentArray_push___redArg(v_traces_109_, v___x_121_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_122_);
v___x_124_ = v___x_111_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_122_);
lean_ctor_set_uint64(v_reuseFailAlloc_132_, sizeof(void*)*1, v_tid_108_);
v___x_124_ = v_reuseFailAlloc_132_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_126_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 4, v___x_124_);
v___x_126_ = v___x_106_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_env_96_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_nextMacroScope_97_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_ngen_98_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_auxDeclNGen_99_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_131_, 5, v_cache_100_);
lean_ctor_set(v_reuseFailAlloc_131_, 6, v_recordedDeps_101_);
lean_ctor_set(v_reuseFailAlloc_131_, 7, v_messages_102_);
lean_ctor_set(v_reuseFailAlloc_131_, 8, v_infoState_103_);
lean_ctor_set(v_reuseFailAlloc_131_, 9, v_snapshotTasks_104_);
v___x_126_ = v_reuseFailAlloc_131_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_st_ref_put(v___y_86_, v___x_126_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_113_);
v___x_129_ = v___x_92_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_113_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg___boxed(lean_object* v_cls_136_, lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v_cls_136_, v_msg_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = l_Lean_Level_ofNat(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_283_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1___closed__1));
v___x_284_ = l_Lean_Name_append(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__62));
v___x_287_ = l_Lean_stringToMessageData(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__64));
v___x_290_ = l_Lean_stringToMessageData(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__77));
v___x_318_ = l_Lean_stringToMessageData(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(lean_object* v_type_319_, lean_object* v_base_320_, lean_object* v_semiringInst_321_, lean_object* v_commSemiringInst_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
lean_inc_ref(v_base_320_);
v___x_330_ = l_Lean_Meta_getDecLevel_x3f(v_base_320_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_785_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_785_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_785_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_785_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
if (lean_obj_tag(v_a_331_) == 1)
{
lean_object* v_val_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_780_; 
lean_del_object(v___x_333_);
v_val_335_ = lean_ctor_get(v_a_331_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_a_331_);
if (v_isSharedCheck_780_ == 0)
{
v___x_337_ = v_a_331_;
v_isShared_338_ = v_isSharedCheck_780_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_val_335_);
lean_dec(v_a_331_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_780_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___y_354_; lean_object* v___y_355_; lean_object* v___y_356_; lean_object* v___y_357_; lean_object* v___y_358_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_339_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__5));
v___x_340_ = lean_box(0);
lean_inc(v_val_335_);
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v_val_335_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_inc_ref_n(v___x_341_, 5);
v___x_342_ = l_Lean_mkConst(v___x_339_, v___x_341_);
lean_inc_ref(v_base_320_);
v___x_343_ = l_Lean_mkAppB(v___x_342_, v_base_320_, v_commSemiringInst_322_);
v___x_344_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7));
v___x_345_ = l_Lean_mkConst(v___x_344_, v___x_341_);
lean_inc_ref_n(v___x_343_, 2);
lean_inc_ref_n(v_type_319_, 4);
v___x_346_ = l_Lean_mkAppB(v___x_345_, v_type_319_, v___x_343_);
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_348_ = l_Lean_mkConst(v___x_347_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_349_ = l_Lean_mkAppB(v___x_348_, v_type_319_, v___x_346_);
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12));
v___x_351_ = l_Lean_mkConst(v___x_350_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_352_ = l_Lean_mkAppB(v___x_351_, v_type_319_, v___x_349_);
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13));
v___x_398_ = l_Lean_mkConst(v___x_397_, v___x_341_);
v___x_399_ = l_Lean_Expr_app___override(v___x_398_, v_type_319_);
v___x_400_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_399_, v___x_343_, v_a_324_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec_ref_known(v___x_400_, 1);
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14));
lean_inc_ref(v___x_341_);
v___x_402_ = l_Lean_mkConst(v___x_401_, v___x_341_);
lean_inc_ref(v_type_319_);
v___x_403_ = l_Lean_Expr_app___override(v___x_402_, v_type_319_);
lean_inc_ref(v___x_346_);
v___x_404_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_403_, v___x_346_, v_a_324_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_dec_ref_known(v___x_404_, 1);
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16));
lean_inc_ref(v___x_341_);
v___x_406_ = l_Lean_mkConst(v___x_405_, v___x_341_);
lean_inc_ref(v_type_319_);
v___x_407_ = l_Lean_Expr_app___override(v___x_406_, v_type_319_);
lean_inc_ref(v___x_349_);
v___x_408_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_407_, v___x_349_, v_a_324_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref_known(v___x_408_, 1);
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18));
lean_inc_ref(v___x_341_);
v___x_410_ = l_Lean_mkConst(v___x_409_, v___x_341_);
lean_inc_ref(v_type_319_);
v___x_411_ = l_Lean_Expr_app___override(v___x_410_, v_type_319_);
lean_inc_ref(v___x_352_);
v___x_412_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_411_, v___x_352_, v_a_324_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref_known(v___x_412_, 1);
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__20));
lean_inc_ref_n(v___x_341_, 2);
v___x_414_ = l_Lean_mkConst(v___x_413_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_415_ = l_Lean_Expr_app___override(v___x_414_, v_type_319_);
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__22));
v___x_417_ = l_Lean_mkConst(v___x_416_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_418_ = l_Lean_mkAppB(v___x_417_, v_type_319_, v___x_349_);
v___x_419_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_415_, v___x_418_, v_a_324_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref_known(v___x_419_, 1);
v___x_420_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__24));
lean_inc_ref_n(v___x_341_, 3);
lean_inc_n(v_val_335_, 2);
v___x_421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_421_, 0, v_val_335_);
lean_ctor_set(v___x_421_, 1, v___x_341_);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v_val_335_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
lean_inc_ref(v___x_422_);
v___x_423_ = l_Lean_mkConst(v___x_420_, v___x_422_);
lean_inc_ref_n(v_type_319_, 5);
v___x_424_ = l_Lean_mkApp3(v___x_423_, v_type_319_, v_type_319_, v_type_319_);
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__26));
v___x_426_ = l_Lean_mkConst(v___x_425_, v___x_341_);
v___x_427_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__28));
v___x_428_ = l_Lean_mkConst(v___x_427_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_429_ = l_Lean_mkAppB(v___x_428_, v_type_319_, v___x_349_);
v___x_430_ = l_Lean_mkAppB(v___x_426_, v_type_319_, v___x_429_);
v___x_431_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_424_, v___x_430_, v_a_324_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec_ref_known(v___x_431_, 1);
v___x_432_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__30));
lean_inc_ref(v___x_422_);
v___x_433_ = l_Lean_mkConst(v___x_432_, v___x_422_);
lean_inc_ref_n(v_type_319_, 5);
v___x_434_ = l_Lean_mkApp3(v___x_433_, v_type_319_, v_type_319_, v_type_319_);
v___x_435_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__32));
lean_inc_ref_n(v___x_341_, 2);
v___x_436_ = l_Lean_mkConst(v___x_435_, v___x_341_);
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__34));
v___x_438_ = l_Lean_mkConst(v___x_437_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_439_ = l_Lean_mkAppB(v___x_438_, v_type_319_, v___x_349_);
v___x_440_ = l_Lean_mkAppB(v___x_436_, v_type_319_, v___x_439_);
v___x_441_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_434_, v___x_440_, v_a_324_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec_ref_known(v___x_441_, 1);
v___x_442_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__36));
v___x_443_ = l_Lean_mkConst(v___x_442_, v___x_422_);
lean_inc_ref_n(v_type_319_, 5);
v___x_444_ = l_Lean_mkApp3(v___x_443_, v_type_319_, v_type_319_, v_type_319_);
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__38));
lean_inc_ref_n(v___x_341_, 2);
v___x_446_ = l_Lean_mkConst(v___x_445_, v___x_341_);
v___x_447_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__40));
v___x_448_ = l_Lean_mkConst(v___x_447_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_449_ = l_Lean_mkAppB(v___x_448_, v_type_319_, v___x_346_);
v___x_450_ = l_Lean_mkAppB(v___x_446_, v_type_319_, v___x_449_);
v___x_451_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_444_, v___x_450_, v_a_324_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec_ref_known(v___x_451_, 1);
v___x_452_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__42));
lean_inc_ref_n(v___x_341_, 2);
v___x_453_ = l_Lean_mkConst(v___x_452_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_454_ = l_Lean_Expr_app___override(v___x_453_, v_type_319_);
v___x_455_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__44));
v___x_456_ = l_Lean_mkConst(v___x_455_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_457_ = l_Lean_mkAppB(v___x_456_, v_type_319_, v___x_346_);
v___x_458_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_454_, v___x_457_, v_a_324_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref_known(v___x_458_, 1);
v___x_459_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__46));
v___x_460_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__47);
lean_inc_ref_n(v___x_341_, 2);
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_341_);
lean_inc(v_val_335_);
v___x_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_462_, 0, v_val_335_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = l_Lean_mkConst(v___x_459_, v___x_462_);
v___x_464_ = l_Lean_Nat_mkType;
lean_inc_ref_n(v_type_319_, 3);
v___x_465_ = l_Lean_mkApp3(v___x_463_, v_type_319_, v___x_464_, v_type_319_);
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__49));
v___x_467_ = l_Lean_mkConst(v___x_466_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_468_ = l_Lean_mkAppB(v___x_467_, v_type_319_, v___x_349_);
v___x_469_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_465_, v___x_468_, v_a_324_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec_ref_known(v___x_469_, 1);
v___x_470_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__51));
lean_inc_ref_n(v___x_341_, 2);
v___x_471_ = l_Lean_mkConst(v___x_470_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_472_ = l_Lean_Expr_app___override(v___x_471_, v_type_319_);
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__53));
v___x_474_ = l_Lean_mkConst(v___x_473_, v___x_341_);
lean_inc_ref(v___x_349_);
v___x_475_ = l_Lean_mkAppB(v___x_474_, v_type_319_, v___x_349_);
v___x_476_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_472_, v___x_475_, v_a_324_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
lean_dec_ref_known(v___x_476_, 1);
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__55));
lean_inc_ref_n(v___x_341_, 2);
v___x_478_ = l_Lean_mkConst(v___x_477_, v___x_341_);
lean_inc_ref_n(v_type_319_, 2);
v___x_479_ = l_Lean_Expr_app___override(v___x_478_, v_type_319_);
v___x_480_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__57));
v___x_481_ = l_Lean_mkConst(v___x_480_, v___x_341_);
lean_inc_ref(v___x_346_);
v___x_482_ = l_Lean_mkAppB(v___x_481_, v_type_319_, v___x_346_);
v___x_483_ = l_Lean_Meta_Sym_registerInstance___redArg(v___x_479_, v___x_482_, v_a_324_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_toCold_484_; lean_object* v_inheritedTraceOptions_485_; lean_object* v___x_486_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v_options_495_; lean_object* v_inheritedTraceOptions_496_; lean_object* v___y_497_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v_noZeroDivInst_x3f_540_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; lean_object* v___y_546_; lean_object* v___y_557_; lean_object* v_val_558_; lean_object* v_charInst_x3f_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v_addRightCancelInst_x3f_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___x_669_; lean_object* v_a_670_; uint8_t v___x_671_; 
lean_dec_ref_known(v___x_483_, 1);
v_toCold_484_ = lean_ctor_get(v_a_327_, 0);
v_inheritedTraceOptions_485_ = lean_ctor_get(v_toCold_484_, 11);
v___x_486_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_669_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_486_, v_inheritedTraceOptions_485_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref(v___x_669_);
v___x_671_ = lean_unbox(v_a_670_);
lean_dec(v_a_670_);
if (v___x_671_ == 0)
{
v___y_635_ = v_a_323_;
v___y_636_ = v_a_324_;
v___y_637_ = v_a_325_;
v___y_638_ = v_a_326_;
v___y_639_ = v_a_327_;
v___y_640_ = v_a_328_;
goto v___jp_634_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_672_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_319_);
v___x_673_ = l_Lean_MessageData_ofExpr(v_type_319_);
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_486_, v___x_674_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_dec_ref_known(v___x_675_, 1);
v___y_635_ = v_a_323_;
v___y_636_ = v_a_324_;
v___y_637_ = v_a_325_;
v___y_638_ = v_a_326_;
v___y_639_ = v_a_327_;
v___y_640_ = v_a_328_;
goto v___jp_634_;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
v___jp_487_:
{
uint8_t v_hasTrace_498_; 
v_hasTrace_498_ = lean_ctor_get_uint8(v_options_495_, sizeof(void*)*1);
if (v_hasTrace_498_ == 0)
{
v___y_354_ = v___y_488_;
v___y_355_ = v___y_489_;
v___y_356_ = v___y_490_;
v___y_357_ = v___y_491_;
v___y_358_ = v___y_494_;
goto v___jp_353_;
}
else
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_500_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_496_, v_options_495_, v___x_499_);
if (v___x_500_ == 0)
{
v___y_354_ = v___y_488_;
v___y_355_ = v___y_489_;
v___y_356_ = v___y_490_;
v___y_357_ = v___y_491_;
v___y_358_ = v___y_494_;
goto v___jp_353_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__63);
v___x_502_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_486_, v___x_501_, v___y_492_, v___y_493_, v___y_494_, v___y_497_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_dec_ref_known(v___x_502_, 1);
v___y_354_ = v___y_488_;
v___y_355_ = v___y_489_;
v___y_356_ = v___y_490_;
v___y_357_ = v___y_491_;
v___y_358_ = v___y_494_;
goto v___jp_353_;
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_type_319_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
v___jp_511_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
lean_inc_ref(v___y_521_);
v___x_522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_522_, 0, v___y_521_);
v___x_523_ = l_Lean_MessageData_ofFormat(v___x_522_);
lean_inc_ref(v___y_516_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___y_516_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_486_, v___x_524_, v___y_513_, v___y_519_, v___y_515_, v___y_518_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_toCold_526_; lean_object* v_options_527_; lean_object* v_inheritedTraceOptions_528_; 
lean_dec_ref_known(v___x_525_, 1);
v_toCold_526_ = lean_ctor_get(v___y_515_, 0);
v_options_527_ = lean_ctor_get(v_toCold_526_, 2);
v_inheritedTraceOptions_528_ = lean_ctor_get(v_toCold_526_, 11);
v___y_488_ = v___y_512_;
v___y_489_ = v___y_514_;
v___y_490_ = v___y_520_;
v___y_491_ = v___y_517_;
v___y_492_ = v___y_513_;
v___y_493_ = v___y_519_;
v___y_494_ = v___y_515_;
v_options_495_ = v_options_527_;
v_inheritedTraceOptions_496_ = v_inheritedTraceOptions_528_;
v___y_497_ = v___y_518_;
goto v___jp_487_;
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v___y_520_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_512_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_type_319_);
v_a_529_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_525_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_525_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
v___jp_537_:
{
lean_object* v_toCold_547_; lean_object* v_options_548_; lean_object* v_inheritedTraceOptions_549_; lean_object* v___x_550_; lean_object* v_a_551_; uint8_t v___x_552_; 
v_toCold_547_ = lean_ctor_get(v___y_545_, 0);
v_options_548_ = lean_ctor_get(v_toCold_547_, 2);
v_inheritedTraceOptions_549_ = lean_ctor_get(v_toCold_547_, 11);
v___x_550_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_486_, v_inheritedTraceOptions_549_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref(v___x_550_);
v___x_552_ = lean_unbox(v_a_551_);
lean_dec(v_a_551_);
if (v___x_552_ == 0)
{
v___y_488_ = v___y_538_;
v___y_489_ = v___y_539_;
v___y_490_ = v_noZeroDivInst_x3f_540_;
v___y_491_ = v___y_542_;
v___y_492_ = v___y_543_;
v___y_493_ = v___y_544_;
v___y_494_ = v___y_545_;
v_options_495_ = v_options_548_;
v_inheritedTraceOptions_496_ = v_inheritedTraceOptions_549_;
v___y_497_ = v___y_546_;
goto v___jp_487_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65);
if (lean_obj_tag(v_noZeroDivInst_x3f_540_) == 0)
{
lean_object* v___x_554_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_512_ = v___y_538_;
v___y_513_ = v___y_543_;
v___y_514_ = v___y_539_;
v___y_515_ = v___y_545_;
v___y_516_ = v___x_553_;
v___y_517_ = v___y_542_;
v___y_518_ = v___y_546_;
v___y_519_ = v___y_544_;
v___y_520_ = v_noZeroDivInst_x3f_540_;
v___y_521_ = v___x_554_;
goto v___jp_511_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_512_ = v___y_538_;
v___y_513_ = v___y_543_;
v___y_514_ = v___y_539_;
v___y_515_ = v___y_545_;
v___y_516_ = v___x_553_;
v___y_517_ = v___y_542_;
v___y_518_ = v___y_546_;
v___y_519_ = v___y_544_;
v___y_520_ = v_noZeroDivInst_x3f_540_;
v___y_521_ = v___x_555_;
goto v___jp_511_;
}
}
}
v___jp_556_:
{
lean_object* v___x_566_; 
lean_inc_ref(v_base_320_);
lean_inc(v_val_335_);
v___x_566_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_val_335_, v_base_320_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
if (lean_obj_tag(v_a_567_) == 1)
{
lean_object* v_val_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_578_; 
v_val_568_ = lean_ctor_get(v_a_567_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_a_567_);
if (v_isSharedCheck_578_ == 0)
{
v___x_570_ = v_a_567_;
v_isShared_571_ = v_isSharedCheck_578_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_val_568_);
lean_dec(v_a_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_578_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__70));
v___x_573_ = l_Lean_mkConst(v___x_572_, v___x_341_);
v___x_574_ = l_Lean_mkApp4(v___x_573_, v_base_320_, v_semiringInst_321_, v_val_558_, v_val_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_574_);
v___x_576_ = v___x_570_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
v___y_538_ = v_charInst_x3f_559_;
v___y_539_ = v___y_557_;
v_noZeroDivInst_x3f_540_ = v___x_576_;
v___y_541_ = v___y_560_;
v___y_542_ = v___y_561_;
v___y_543_ = v___y_562_;
v___y_544_ = v___y_563_;
v___y_545_ = v___y_564_;
v___y_546_ = v___y_565_;
goto v___jp_537_;
}
}
}
else
{
lean_object* v___x_579_; 
lean_dec(v_a_567_);
lean_dec_ref(v_val_558_);
lean_dec_ref_known(v___x_341_, 2);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
v___x_579_ = lean_box(0);
v___y_538_ = v_charInst_x3f_559_;
v___y_539_ = v___y_557_;
v_noZeroDivInst_x3f_540_ = v___x_579_;
v___y_541_ = v___y_560_;
v___y_542_ = v___y_561_;
v___y_543_ = v___y_562_;
v___y_544_ = v___y_563_;
v___y_545_ = v___y_564_;
v___y_546_ = v___y_565_;
goto v___jp_537_;
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_charInst_x3f_559_);
lean_dec_ref(v_val_558_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_580_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_566_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_566_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
v___jp_588_:
{
lean_object* v___x_596_; 
lean_inc_ref(v_semiringInst_321_);
lean_inc_ref(v_base_320_);
lean_inc(v_val_335_);
v___x_596_ = l_Lean_Meta_Sym_Arith_getCharInfo(v_val_335_, v_base_320_, v_semiringInst_321_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_596_) == 0)
{
if (lean_obj_tag(v_addRightCancelInst_x3f_589_) == 1)
{
lean_object* v_a_597_; lean_object* v_inst_x3f_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v_inst_x3f_598_ = lean_ctor_get(v_a_597_, 0);
lean_inc(v_inst_x3f_598_);
if (lean_obj_tag(v_inst_x3f_598_) == 1)
{
lean_object* v_val_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_620_; 
v_val_599_ = lean_ctor_get(v_inst_x3f_598_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v_inst_x3f_598_);
if (v_isSharedCheck_620_ == 0)
{
v___x_601_ = v_inst_x3f_598_;
v_isShared_602_ = v_isSharedCheck_620_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_val_599_);
lean_dec(v_inst_x3f_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_620_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_val_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_619_; 
v_val_603_ = lean_ctor_get(v_addRightCancelInst_x3f_589_, 0);
lean_inc(v_val_603_);
lean_dec_ref_known(v_addRightCancelInst_x3f_589_, 1);
v_fst_604_ = lean_ctor_get(v_val_599_, 0);
v_snd_605_ = lean_ctor_get(v_val_599_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_val_599_);
if (v_isSharedCheck_619_ == 0)
{
v___x_607_ = v_val_599_;
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_inc(v_fst_604_);
lean_dec(v_val_599_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_619_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_609_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__72));
lean_inc_ref(v___x_341_);
v___x_610_ = l_Lean_mkConst(v___x_609_, v___x_341_);
lean_inc(v_snd_605_);
v___x_611_ = l_Lean_mkRawNatLit(v_snd_605_);
lean_inc(v_val_603_);
lean_inc_ref(v_semiringInst_321_);
lean_inc_ref(v_base_320_);
v___x_612_ = l_Lean_mkApp5(v___x_610_, v_base_320_, v___x_611_, v_semiringInst_321_, v_val_603_, v_fst_604_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_612_);
v___x_614_ = v___x_607_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_snd_605_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_614_);
v___x_616_ = v___x_601_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
v___y_557_ = v_a_597_;
v_val_558_ = v_val_603_;
v_charInst_x3f_559_ = v___x_616_;
v___y_560_ = v___y_590_;
v___y_561_ = v___y_591_;
v___y_562_ = v___y_592_;
v___y_563_ = v___y_593_;
v___y_564_ = v___y_594_;
v___y_565_ = v___y_595_;
goto v___jp_556_;
}
}
}
}
}
else
{
lean_object* v_val_621_; lean_object* v___x_622_; 
lean_dec(v_inst_x3f_598_);
v_val_621_ = lean_ctor_get(v_addRightCancelInst_x3f_589_, 0);
lean_inc(v_val_621_);
lean_dec_ref_known(v_addRightCancelInst_x3f_589_, 1);
v___x_622_ = lean_box(0);
v___y_557_ = v_a_597_;
v_val_558_ = v_val_621_;
v_charInst_x3f_559_ = v___x_622_;
v___y_560_ = v___y_590_;
v___y_561_ = v___y_591_;
v___y_562_ = v___y_592_;
v___y_563_ = v___y_593_;
v___y_564_ = v___y_594_;
v___y_565_ = v___y_595_;
goto v___jp_556_;
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_596_, 1);
v___x_624_ = lean_box(0);
if (lean_obj_tag(v_addRightCancelInst_x3f_589_) == 1)
{
lean_object* v_val_625_; 
v_val_625_ = lean_ctor_get(v_addRightCancelInst_x3f_589_, 0);
lean_inc(v_val_625_);
lean_dec_ref_known(v_addRightCancelInst_x3f_589_, 1);
v___y_557_ = v_a_623_;
v_val_558_ = v_val_625_;
v_charInst_x3f_559_ = v___x_624_;
v___y_560_ = v___y_590_;
v___y_561_ = v___y_591_;
v___y_562_ = v___y_592_;
v___y_563_ = v___y_593_;
v___y_564_ = v___y_594_;
v___y_565_ = v___y_595_;
goto v___jp_556_;
}
else
{
lean_dec(v_addRightCancelInst_x3f_589_);
lean_dec_ref_known(v___x_341_, 2);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
v___y_538_ = v___x_624_;
v___y_539_ = v_a_623_;
v_noZeroDivInst_x3f_540_ = v___x_624_;
v___y_541_ = v___y_590_;
v___y_542_ = v___y_591_;
v___y_543_ = v___y_592_;
v___y_544_ = v___y_593_;
v___y_545_ = v___y_594_;
v___y_546_ = v___y_595_;
goto v___jp_537_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_addRightCancelInst_x3f_589_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_626_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_596_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_596_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
v___jp_634_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_641_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__74));
lean_inc_ref(v___x_341_);
v___x_642_ = l_Lean_mkConst(v___x_641_, v___x_341_);
lean_inc_ref(v_base_320_);
v___x_643_ = l_Lean_Expr_app___override(v___x_642_, v_base_320_);
v___x_644_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_643_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
if (lean_obj_tag(v_a_645_) == 1)
{
lean_object* v_val_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_val_646_ = lean_ctor_get(v_a_645_, 0);
lean_inc(v_val_646_);
lean_dec_ref_known(v_a_645_, 1);
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__76));
lean_inc_ref(v___x_341_);
v___x_648_ = l_Lean_mkConst(v___x_647_, v___x_341_);
lean_inc_ref(v_base_320_);
v___x_649_ = l_Lean_mkAppB(v___x_648_, v_base_320_, v_val_646_);
v___x_650_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_649_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v_addRightCancelInst_x3f_589_ = v_a_651_;
v___y_590_ = v___y_635_;
v___y_591_ = v___y_636_;
v___y_592_ = v___y_637_;
v___y_593_ = v___y_638_;
v___y_594_ = v___y_639_;
v___y_595_ = v___y_640_;
goto v___jp_588_;
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_652_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v___x_660_; 
lean_dec(v_a_645_);
v___x_660_ = lean_box(0);
v_addRightCancelInst_x3f_589_ = v___x_660_;
v___y_590_ = v___y_635_;
v___y_591_ = v___y_636_;
v___y_592_ = v___y_637_;
v___y_593_ = v___y_638_;
v___y_594_ = v___y_639_;
v___y_595_ = v___y_640_;
goto v___jp_588_;
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_661_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_644_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_644_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_684_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_483_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_483_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_692_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_476_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_476_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_700_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_469_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_469_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_708_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_458_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_458_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_716_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_451_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_451_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
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
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref_known(v___x_422_, 2);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_724_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_441_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_441_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref_known(v___x_422_, 2);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_732_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_431_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_431_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_740_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_419_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_419_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_748_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_412_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_412_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_756_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_408_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_408_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_764_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_404_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_404_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_dec_ref_known(v___x_341_, 2);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_772_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_400_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_400_);
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
v___jp_353_:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_357_, v___y_358_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v_rings_361_; uint8_t v_symbolic_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___f_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v_rings_361_ = lean_ctor_get(v_a_360_, 1);
lean_inc_ref(v_rings_361_);
lean_dec(v_a_360_);
v_symbolic_362_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*1);
lean_dec_ref(v___y_355_);
v___x_363_ = lean_array_get_size(v_rings_361_);
lean_dec_ref(v_rings_361_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set(v___x_365_, 1, v_type_319_);
lean_ctor_set(v___x_365_, 2, v_val_335_);
lean_ctor_set(v___x_365_, 3, v___x_346_);
lean_ctor_set(v___x_365_, 4, v___x_349_);
lean_ctor_set(v___x_365_, 5, v___y_354_);
lean_ctor_set(v___x_365_, 6, v___x_364_);
lean_ctor_set(v___x_365_, 7, v___x_364_);
lean_ctor_set(v___x_365_, 8, v___x_364_);
lean_ctor_set(v___x_365_, 9, v___x_364_);
lean_ctor_set(v___x_365_, 10, v___x_364_);
lean_ctor_set(v___x_365_, 11, v___x_364_);
lean_ctor_set(v___x_365_, 12, v___x_364_);
lean_ctor_set(v___x_365_, 13, v___x_364_);
lean_ctor_set(v___x_365_, 14, v___x_364_);
lean_ctor_set(v___x_365_, 15, v___x_364_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*16, v_symbolic_362_);
v___x_366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
lean_ctor_set(v___x_366_, 2, v___x_364_);
lean_ctor_set(v___x_366_, 3, v___x_364_);
lean_ctor_set(v___x_366_, 4, v___x_352_);
lean_ctor_set(v___x_366_, 5, v___x_343_);
lean_ctor_set(v___x_366_, 6, v___y_356_);
lean_ctor_set(v___x_366_, 7, v___x_364_);
lean_ctor_set(v___x_366_, 8, v___x_364_);
v___f_367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0), 2, 1);
lean_closure_set(v___f_367_, 0, v___x_366_);
v___x_368_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_369_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_368_, v___f_367_, v___y_357_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_379_; 
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_369_, 0);
lean_dec(v_unused_380_);
v___x_371_ = v___x_369_;
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
else
{
lean_dec(v___x_369_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_379_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_363_);
v___x_374_ = v___x_337_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_363_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_del_object(v___x_337_);
v_a_381_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_369_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_369_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___x_352_);
lean_dec_ref(v___x_349_);
lean_dec_ref(v___x_346_);
lean_dec_ref(v___x_343_);
lean_del_object(v___x_337_);
lean_dec(v_val_335_);
lean_dec_ref(v_type_319_);
v_a_389_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_359_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_359_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_783_; 
lean_dec(v_a_331_);
lean_dec_ref(v_commSemiringInst_322_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v___x_781_ = lean_box(0);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_781_);
v___x_783_ = v___x_333_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_commSemiringInst_322_);
lean_dec_ref(v_semiringInst_321_);
lean_dec_ref(v_base_320_);
lean_dec_ref(v_type_319_);
v_a_786_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_330_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_330_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___boxed(lean_object* v_type_794_, lean_object* v_base_795_, lean_object* v_semiringInst_796_, lean_object* v_commSemiringInst_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(v_type_794_, v_base_795_, v_semiringInst_796_, v_commSemiringInst_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(lean_object* v_cls_806_, lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v_cls_806_, v_msg_807_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___boxed(lean_object* v_cls_816_, lean_object* v_msg_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0(v_cls_816_, v_msg_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_825_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__2));
v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(lean_object* v_type_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; 
lean_inc_ref(v_type_834_);
v___x_842_ = l_Lean_Meta_getDecLevel_x3f(v_type_834_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_1083_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_1083_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_1083_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
if (lean_obj_tag(v_a_843_) == 1)
{
lean_object* v_val_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_1078_; 
lean_del_object(v___x_845_);
v_val_847_ = lean_ctor_get(v_a_843_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_a_843_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_849_ = v_a_843_;
v_isShared_850_ = v_isSharedCheck_1078_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_val_847_);
lean_dec(v_a_843_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_1078_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__13));
v___x_852_ = lean_box(0);
lean_inc(v_val_847_);
v___x_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_853_, 0, v_val_847_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
lean_inc_ref(v___x_853_);
v___x_854_ = l_Lean_mkConst(v___x_851_, v___x_853_);
lean_inc_ref(v_type_834_);
v___x_855_ = l_Lean_Expr_app___override(v___x_854_, v_type_834_);
v___x_856_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_855_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_1069_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_1069_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_1069_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
if (lean_obj_tag(v_a_857_) == 1)
{
lean_object* v_val_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_1064_; 
lean_del_object(v___x_859_);
v_val_861_ = lean_ctor_get(v_a_857_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_a_857_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_863_ = v_a_857_;
v_isShared_864_ = v_isSharedCheck_1064_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_val_861_);
lean_dec(v_a_857_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_1064_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_toCold_868_; lean_object* v_inheritedTraceOptions_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___x_922_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___x_1049_; lean_object* v_a_1050_; uint8_t v___x_1051_; 
v___x_865_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__7));
lean_inc_ref_n(v___x_853_, 3);
v___x_866_ = l_Lean_mkConst(v___x_865_, v___x_853_);
lean_inc(v_val_861_);
lean_inc_ref_n(v_type_834_, 3);
v___x_867_ = l_Lean_mkAppB(v___x_866_, v_type_834_, v_val_861_);
v_toCold_868_ = lean_ctor_get(v_a_839_, 0);
v_inheritedTraceOptions_869_ = lean_ctor_get(v_toCold_868_, 11);
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_871_ = l_Lean_mkConst(v___x_870_, v___x_853_);
lean_inc_ref(v___x_867_);
v___x_872_ = l_Lean_mkAppB(v___x_871_, v_type_834_, v___x_867_);
v___x_873_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__12));
v___x_874_ = l_Lean_mkConst(v___x_873_, v___x_853_);
lean_inc_ref(v___x_872_);
v___x_875_ = l_Lean_mkAppB(v___x_874_, v_type_834_, v___x_872_);
v___x_922_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_1049_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_922_, v_inheritedTraceOptions_869_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref(v___x_1049_);
v___x_1051_ = lean_unbox(v_a_1050_);
lean_dec(v_a_1050_);
if (v___x_1051_ == 0)
{
v___y_1015_ = v_a_835_;
v___y_1016_ = v_a_836_;
v___y_1017_ = v_a_837_;
v___y_1018_ = v_a_838_;
v___y_1019_ = v_a_839_;
v___y_1020_ = v_a_840_;
goto v___jp_1014_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1052_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_834_);
v___x_1053_ = l_Lean_MessageData_ofExpr(v_type_834_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_922_, v___x_1054_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_dec_ref_known(v___x_1055_, 1);
v___y_1015_ = v_a_835_;
v___y_1016_ = v_a_836_;
v___y_1017_ = v_a_837_;
v___y_1018_ = v_a_838_;
v___y_1019_ = v_a_839_;
v___y_1020_ = v_a_840_;
goto v___jp_1014_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_867_);
lean_del_object(v___x_863_);
lean_dec(v_val_861_);
lean_dec_ref_known(v___x_853_, 2);
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
v___jp_876_:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_box(0);
v___x_884_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v_rings_886_; lean_object* v_inst_x3f_887_; uint8_t v_symbolic_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v_rings_886_ = lean_ctor_get(v_a_885_, 1);
lean_inc_ref(v_rings_886_);
lean_dec(v_a_885_);
v_inst_x3f_887_ = lean_ctor_get(v___y_877_, 0);
lean_inc(v_inst_x3f_887_);
v_symbolic_888_ = lean_ctor_get_uint8(v___y_877_, sizeof(void*)*1);
lean_dec_ref(v___y_877_);
v___x_889_ = lean_array_get_size(v_rings_886_);
lean_dec_ref(v_rings_886_);
v___x_890_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_type_834_);
lean_ctor_set(v___x_890_, 2, v_val_847_);
lean_ctor_set(v___x_890_, 3, v___x_867_);
lean_ctor_set(v___x_890_, 4, v___x_872_);
lean_ctor_set(v___x_890_, 5, v_inst_x3f_887_);
lean_ctor_set(v___x_890_, 6, v___x_883_);
lean_ctor_set(v___x_890_, 7, v___x_883_);
lean_ctor_set(v___x_890_, 8, v___x_883_);
lean_ctor_set(v___x_890_, 9, v___x_883_);
lean_ctor_set(v___x_890_, 10, v___x_883_);
lean_ctor_set(v___x_890_, 11, v___x_883_);
lean_ctor_set(v___x_890_, 12, v___x_883_);
lean_ctor_set(v___x_890_, 13, v___x_883_);
lean_ctor_set(v___x_890_, 14, v___x_883_);
lean_ctor_set(v___x_890_, 15, v___x_883_);
lean_ctor_set_uint8(v___x_890_, sizeof(void*)*16, v_symbolic_888_);
v___x_891_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v___x_883_);
lean_ctor_set(v___x_891_, 2, v___x_883_);
lean_ctor_set(v___x_891_, 3, v___x_883_);
lean_ctor_set(v___x_891_, 4, v___x_875_);
lean_ctor_set(v___x_891_, 5, v_val_861_);
lean_ctor_set(v___x_891_, 6, v___y_880_);
lean_ctor_set(v___x_891_, 7, v___y_879_);
lean_ctor_set(v___x_891_, 8, v___y_878_);
v___f_892_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__0), 2, 1);
lean_closure_set(v___f_892_, 0, v___x_891_);
v___x_893_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_894_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_893_, v___f_892_, v___y_881_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_904_; 
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v___x_894_, 0);
lean_dec(v_unused_905_);
v___x_896_ = v___x_894_;
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
else
{
lean_dec(v___x_894_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_904_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_889_);
v___x_899_ = v___x_863_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_889_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_899_);
v___x_901_ = v___x_896_;
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
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_del_object(v___x_863_);
v_a_906_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_894_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_894_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_867_);
lean_del_object(v___x_863_);
lean_dec(v_val_861_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v_a_914_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_884_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_884_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
v___jp_923_:
{
lean_object* v___x_936_; 
lean_inc_ref(v___y_934_);
if (v_isShared_850_ == 0)
{
lean_ctor_set_tag(v___x_849_, 3);
lean_ctor_set(v___x_849_, 0, v___y_934_);
v___x_936_ = v___x_849_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___y_934_);
v___x_936_ = v_reuseFailAlloc_948_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = l_Lean_MessageData_ofFormat(v___x_936_);
lean_inc_ref(v___y_932_);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___y_932_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_922_, v___x_938_, v___y_931_, v___y_925_, v___y_927_, v___y_928_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_dec_ref_known(v___x_939_, 1);
v___y_877_ = v___y_924_;
v___y_878_ = v___y_926_;
v___y_879_ = v___y_930_;
v___y_880_ = v___y_929_;
v___y_881_ = v___y_933_;
v___y_882_ = v___y_927_;
goto v___jp_876_;
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_924_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_867_);
lean_del_object(v___x_863_);
lean_dec(v_val_861_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_939_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
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
v___jp_949_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_958_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__1));
v___x_959_ = l_Lean_mkConst(v___x_958_, v___x_853_);
lean_inc_ref(v_type_834_);
v___x_960_ = l_Lean_Expr_app___override(v___x_959_, v_type_834_);
v___x_961_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_960_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
lean_inc_ref(v_type_834_);
lean_inc(v_val_847_);
v___x_963_ = l_Lean_Meta_Sym_Arith_getPowIdentityInst_x3f(v_val_847_, v_type_834_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_toCold_964_; lean_object* v_options_965_; uint8_t v_hasTrace_966_; 
v_toCold_964_ = lean_ctor_get(v___y_956_, 0);
v_options_965_ = lean_ctor_get(v_toCold_964_, 2);
v_hasTrace_966_ = lean_ctor_get_uint8(v_options_965_, sizeof(void*)*1);
if (v_hasTrace_966_ == 0)
{
lean_object* v_a_967_; 
lean_del_object(v___x_849_);
v_a_967_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_963_, 1);
v___y_877_ = v___y_950_;
v___y_878_ = v_a_967_;
v___y_879_ = v_a_962_;
v___y_880_ = v___y_951_;
v___y_881_ = v___y_953_;
v___y_882_ = v___y_956_;
goto v___jp_876_;
}
else
{
lean_object* v_a_968_; lean_object* v_inheritedTraceOptions_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_a_968_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_963_, 1);
v_inheritedTraceOptions_969_ = lean_ctor_get(v_toCold_964_, 11);
v___x_970_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_969_, v_options_965_, v___x_970_);
if (v___x_971_ == 0)
{
lean_del_object(v___x_849_);
v___y_877_ = v___y_950_;
v___y_878_ = v_a_968_;
v___y_879_ = v_a_962_;
v___y_880_ = v___y_951_;
v___y_881_ = v___y_953_;
v___y_882_ = v___y_956_;
goto v___jp_876_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___closed__3);
if (lean_obj_tag(v_a_968_) == 0)
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_924_ = v___y_950_;
v___y_925_ = v___y_955_;
v___y_926_ = v_a_968_;
v___y_927_ = v___y_956_;
v___y_928_ = v___y_957_;
v___y_929_ = v___y_951_;
v___y_930_ = v_a_962_;
v___y_931_ = v___y_954_;
v___y_932_ = v___x_972_;
v___y_933_ = v___y_953_;
v___y_934_ = v___x_973_;
goto v___jp_923_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_924_ = v___y_950_;
v___y_925_ = v___y_955_;
v___y_926_ = v_a_968_;
v___y_927_ = v___y_956_;
v___y_928_ = v___y_957_;
v___y_929_ = v___y_951_;
v___y_930_ = v_a_962_;
v___y_931_ = v___y_954_;
v___y_932_ = v___x_972_;
v___y_933_ = v___y_953_;
v___y_934_ = v___x_974_;
goto v___jp_923_;
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_962_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_867_);
lean_del_object(v___x_863_);
lean_dec(v_val_861_);
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v_a_975_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_963_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_963_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_867_);
lean_del_object(v___x_863_);
lean_dec(v_val_861_);
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v_a_983_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_961_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_961_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
v___jp_991_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
lean_inc_ref(v___y_1001_);
v___x_1002_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___y_1001_);
v___x_1003_ = l_Lean_MessageData_ofFormat(v___x_1002_);
lean_inc_ref(v___y_1000_);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___y_1000_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_922_, v___x_1004_, v___y_995_, v___y_998_, v___y_997_, v___y_993_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_dec_ref_known(v___x_1005_, 1);
v___y_950_ = v___y_992_;
v___y_951_ = v___y_999_;
v___y_952_ = v___y_994_;
v___y_953_ = v___y_996_;
v___y_954_ = v___y_995_;
v___y_955_ = v___y_998_;
v___y_956_ = v___y_997_;
v___y_957_ = v___y_993_;
goto v___jp_949_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
lean_dec(v___y_999_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_867_);
lean_del_object(v___x_863_);
lean_dec(v_val_861_);
lean_dec_ref_known(v___x_853_, 2);
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
v___jp_1014_:
{
lean_object* v___x_1021_; 
lean_inc_ref(v___x_872_);
lean_inc_ref(v_type_834_);
lean_inc(v_val_847_);
v___x_1021_ = l_Lean_Meta_Sym_Arith_getCharInfo(v_val_847_, v_type_834_, v___x_872_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
lean_inc_ref(v_type_834_);
lean_inc(v_val_847_);
v___x_1023_ = l_Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_val_847_, v_type_834_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_toCold_1024_; lean_object* v_a_1025_; lean_object* v_inheritedTraceOptions_1026_; lean_object* v___x_1027_; lean_object* v_a_1028_; uint8_t v___x_1029_; 
v_toCold_1024_ = lean_ctor_get(v___y_1019_, 0);
v_a_1025_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1023_, 1);
v_inheritedTraceOptions_1026_ = lean_ctor_get(v_toCold_1024_, 11);
v___x_1027_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___lam__1(v___x_922_, v_inheritedTraceOptions_1026_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref(v___x_1027_);
v___x_1029_ = lean_unbox(v_a_1028_);
lean_dec(v_a_1028_);
if (v___x_1029_ == 0)
{
v___y_950_ = v_a_1022_;
v___y_951_ = v_a_1025_;
v___y_952_ = v___y_1015_;
v___y_953_ = v___y_1016_;
v___y_954_ = v___y_1017_;
v___y_955_ = v___y_1018_;
v___y_956_ = v___y_1019_;
v___y_957_ = v___y_1020_;
goto v___jp_949_;
}
else
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__65);
if (lean_obj_tag(v_a_1025_) == 0)
{
lean_object* v___x_1031_; 
v___x_1031_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__66));
v___y_992_ = v_a_1022_;
v___y_993_ = v___y_1020_;
v___y_994_ = v___y_1015_;
v___y_995_ = v___y_1017_;
v___y_996_ = v___y_1016_;
v___y_997_ = v___y_1019_;
v___y_998_ = v___y_1018_;
v___y_999_ = v_a_1025_;
v___y_1000_ = v___x_1030_;
v___y_1001_ = v___x_1031_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1032_; 
v___x_1032_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__67));
v___y_992_ = v_a_1022_;
v___y_993_ = v___y_1020_;
v___y_994_ = v___y_1015_;
v___y_995_ = v___y_1017_;
v___y_996_ = v___y_1016_;
v___y_997_ = v___y_1019_;
v___y_998_ = v___y_1018_;
v___y_999_ = v_a_1025_;
v___y_1000_ = v___x_1030_;
v___y_1001_ = v___x_1032_;
goto v___jp_991_;
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec(v_a_1022_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_867_);
lean_del_object(v___x_863_);
lean_dec(v_val_861_);
lean_dec_ref_known(v___x_853_, 2);
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v_a_1033_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1023_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1023_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_dec_ref(v___x_875_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v___x_867_);
lean_del_object(v___x_863_);
lean_dec(v_val_861_);
lean_dec_ref_known(v___x_853_, 2);
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v_a_1041_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1021_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1021_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
}
else
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_dec(v_a_857_);
lean_dec_ref_known(v___x_853_, 2);
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v___x_1065_ = lean_box(0);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_1065_);
v___x_1067_ = v___x_859_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref_known(v___x_853_, 2);
lean_del_object(v___x_849_);
lean_dec(v_val_847_);
lean_dec_ref(v_type_834_);
v_a_1070_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_856_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_856_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
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
else
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_dec(v_a_843_);
lean_dec_ref(v_type_834_);
v___x_1079_ = lean_box(0);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_1079_);
v___x_1081_ = v___x_845_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec_ref(v_type_834_);
v_a_1084_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_842_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_842_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f___boxed(lean_object* v_type_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(lean_object* v_type_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v___x_1121_; uint8_t v___x_1122_; 
lean_inc_ref(v_type_1113_);
v___x_1121_ = l_Lean_Expr_cleanupAnnotations(v_type_1113_);
v___x_1122_ = l_Lean_Expr_isApp(v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1121_);
v___x_1123_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
return v___x_1123_;
}
else
{
lean_object* v_arg_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_arg_1124_ = lean_ctor_get(v___x_1121_, 1);
lean_inc_ref(v_arg_1124_);
v___x_1125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1121_);
v___x_1126_ = l_Lean_Expr_isApp(v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref(v___x_1125_);
lean_dec_ref(v_arg_1124_);
v___x_1127_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
return v___x_1127_;
}
else
{
lean_object* v_arg_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v_arg_1128_ = lean_ctor_get(v___x_1125_, 1);
lean_inc_ref(v_arg_1128_);
v___x_1129_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1125_);
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1));
v___x_1131_ = l_Lean_Expr_isConstOf(v___x_1129_, v___x_1130_);
lean_dec_ref(v___x_1129_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
lean_dec_ref(v_arg_1128_);
lean_dec_ref(v_arg_1124_);
v___x_1132_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
return v___x_1132_;
}
else
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
lean_inc_ref(v_arg_1124_);
v___x_1133_ = l_Lean_Expr_cleanupAnnotations(v_arg_1124_);
v___x_1134_ = l_Lean_Expr_isApp(v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref(v___x_1133_);
lean_dec_ref(v_arg_1128_);
lean_dec_ref(v_arg_1124_);
v___x_1135_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
return v___x_1135_;
}
else
{
lean_object* v_arg_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_arg_1136_ = lean_ctor_get(v___x_1133_, 1);
lean_inc_ref(v_arg_1136_);
v___x_1137_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1133_);
v___x_1138_ = l_Lean_Expr_isApp(v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec_ref(v___x_1137_);
lean_dec_ref(v_arg_1136_);
lean_dec_ref(v_arg_1128_);
lean_dec_ref(v_arg_1124_);
v___x_1139_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1137_);
v___x_1141_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2));
v___x_1142_ = l_Lean_Expr_isConstOf(v___x_1140_, v___x_1141_);
lean_dec_ref(v___x_1140_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref(v_arg_1136_);
lean_dec_ref(v_arg_1128_);
lean_dec_ref(v_arg_1124_);
v___x_1143_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingCore_x3f(v_type_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; 
v___x_1144_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f(v_type_1113_, v_arg_1128_, v_arg_1124_, v_arg_1136_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
return v___x_1144_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(lean_object* v_type_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(lean_object* v___x_1154_, lean_object* v_s_1155_){
_start:
{
lean_object* v_exp_1156_; lean_object* v_rings_1157_; lean_object* v_semirings_1158_; lean_object* v_ncRings_1159_; lean_object* v_ncSemirings_1160_; lean_object* v_typeClassify_1161_; lean_object* v_orders_1162_; lean_object* v_typeOrderClassify_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1171_; 
v_exp_1156_ = lean_ctor_get(v_s_1155_, 0);
v_rings_1157_ = lean_ctor_get(v_s_1155_, 1);
v_semirings_1158_ = lean_ctor_get(v_s_1155_, 2);
v_ncRings_1159_ = lean_ctor_get(v_s_1155_, 3);
v_ncSemirings_1160_ = lean_ctor_get(v_s_1155_, 4);
v_typeClassify_1161_ = lean_ctor_get(v_s_1155_, 5);
v_orders_1162_ = lean_ctor_get(v_s_1155_, 6);
v_typeOrderClassify_1163_ = lean_ctor_get(v_s_1155_, 7);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_s_1155_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1165_ = v_s_1155_;
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_typeOrderClassify_1163_);
lean_inc(v_orders_1162_);
lean_inc(v_typeClassify_1161_);
lean_inc(v_ncSemirings_1160_);
lean_inc(v_ncRings_1159_);
lean_inc(v_semirings_1158_);
lean_inc(v_rings_1157_);
lean_inc(v_exp_1156_);
lean_dec(v_s_1155_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_array_push(v_ncRings_1159_, v___x_1154_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 3, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_exp_1156_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_rings_1157_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_semirings_1158_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_ncSemirings_1160_);
lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_typeClassify_1161_);
lean_ctor_set(v_reuseFailAlloc_1170_, 6, v_orders_1162_);
lean_ctor_set(v_reuseFailAlloc_1170_, 7, v_typeOrderClassify_1163_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(lean_object* v_type_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v___x_1180_; 
lean_inc_ref(v_type_1172_);
v___x_1180_ = l_Lean_Meta_getDecLevel_x3f(v_type_1172_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1295_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1295_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1295_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
if (lean_obj_tag(v_a_1181_) == 1)
{
lean_object* v_val_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_del_object(v___x_1183_);
v_val_1185_ = lean_ctor_get(v_a_1181_, 0);
lean_inc_n(v_val_1185_, 2);
lean_dec_ref_known(v_a_1181_, 1);
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__14));
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1188_, 0, v_val_1185_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
lean_inc_ref(v___x_1188_);
v___x_1189_ = l_Lean_mkConst(v___x_1186_, v___x_1188_);
lean_inc_ref(v_type_1172_);
v___x_1190_ = l_Lean_Expr_app___override(v___x_1189_, v_type_1172_);
v___x_1191_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1190_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1282_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1282_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1282_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
if (lean_obj_tag(v_a_1192_) == 1)
{
lean_object* v_toCold_1196_; lean_object* v_options_1197_; lean_object* v_val_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1277_; 
lean_del_object(v___x_1194_);
v_toCold_1196_ = lean_ctor_get(v_a_1177_, 0);
v_options_1197_ = lean_ctor_get(v_toCold_1196_, 2);
v_val_1198_ = lean_ctor_get(v_a_1192_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_a_1192_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1200_ = v_a_1192_;
v_isShared_1201_ = v_isSharedCheck_1277_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_val_1198_);
lean_dec(v_a_1192_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1277_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_inheritedTraceOptions_1202_; uint8_t v_hasTrace_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; 
v_inheritedTraceOptions_1202_ = lean_ctor_get(v_toCold_1196_, 11);
v_hasTrace_1203_ = lean_ctor_get_uint8(v_options_1197_, sizeof(void*)*1);
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__10));
v___x_1205_ = l_Lean_mkConst(v___x_1204_, v___x_1188_);
lean_inc(v_val_1198_);
lean_inc_ref(v_type_1172_);
v___x_1206_ = l_Lean_mkAppB(v___x_1205_, v_type_1172_, v_val_1198_);
if (v_hasTrace_1203_ == 0)
{
v___y_1208_ = v_a_1173_;
v___y_1209_ = v_a_1174_;
v___y_1210_ = v_a_1175_;
v___y_1211_ = v_a_1176_;
v___y_1212_ = v_a_1177_;
v___y_1213_ = v_a_1178_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__60));
v___x_1263_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__61);
v___x_1264_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1202_, v_options_1197_, v___x_1263_);
if (v___x_1264_ == 0)
{
v___y_1208_ = v_a_1173_;
v___y_1209_ = v_a_1174_;
v___y_1210_ = v_a_1175_;
v___y_1211_ = v_a_1176_;
v___y_1212_ = v_a_1177_;
v___y_1213_ = v_a_1178_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1265_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__78);
lean_inc_ref(v_type_1172_);
v___x_1266_ = l_Lean_MessageData_ofExpr(v_type_1172_);
v___x_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_addTrace___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f_spec__0___redArg(v___x_1262_, v___x_1267_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_dec_ref_known(v___x_1268_, 1);
v___y_1208_ = v_a_1173_;
v___y_1209_ = v_a_1174_;
v___y_1210_ = v_a_1175_;
v___y_1211_ = v_a_1176_;
v___y_1212_ = v_a_1177_;
v___y_1213_ = v_a_1178_;
goto v___jp_1207_;
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v___x_1206_);
lean_del_object(v___x_1200_);
lean_dec(v_val_1198_);
lean_dec(v_val_1185_);
lean_dec_ref(v_type_1172_);
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
v___jp_1207_:
{
lean_object* v___x_1214_; 
lean_inc_ref(v___x_1206_);
lean_inc_ref(v_type_1172_);
lean_inc(v_val_1185_);
v___x_1214_ = l_Lean_Meta_Sym_Arith_getCharInfo(v_val_1185_, v_type_1172_, v___x_1206_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_1209_, v___y_1212_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v_ncRings_1218_; lean_object* v_inst_x3f_1219_; uint8_t v_symbolic_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v___x_1216_, 1);
v_ncRings_1218_ = lean_ctor_get(v_a_1217_, 3);
lean_inc_ref(v_ncRings_1218_);
lean_dec(v_a_1217_);
v_inst_x3f_1219_ = lean_ctor_get(v_a_1215_, 0);
lean_inc(v_inst_x3f_1219_);
v_symbolic_1220_ = lean_ctor_get_uint8(v_a_1215_, sizeof(void*)*1);
lean_dec(v_a_1215_);
v___x_1221_ = lean_array_get_size(v_ncRings_1218_);
lean_dec_ref(v_ncRings_1218_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v_type_1172_);
lean_ctor_set(v___x_1223_, 2, v_val_1185_);
lean_ctor_set(v___x_1223_, 3, v_val_1198_);
lean_ctor_set(v___x_1223_, 4, v___x_1206_);
lean_ctor_set(v___x_1223_, 5, v_inst_x3f_1219_);
lean_ctor_set(v___x_1223_, 6, v___x_1222_);
lean_ctor_set(v___x_1223_, 7, v___x_1222_);
lean_ctor_set(v___x_1223_, 8, v___x_1222_);
lean_ctor_set(v___x_1223_, 9, v___x_1222_);
lean_ctor_set(v___x_1223_, 10, v___x_1222_);
lean_ctor_set(v___x_1223_, 11, v___x_1222_);
lean_ctor_set(v___x_1223_, 12, v___x_1222_);
lean_ctor_set(v___x_1223_, 13, v___x_1222_);
lean_ctor_set(v___x_1223_, 14, v___x_1222_);
lean_ctor_set(v___x_1223_, 15, v___x_1222_);
lean_ctor_set_uint8(v___x_1223_, sizeof(void*)*16, v_symbolic_1220_);
v___f_1224_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0), 2, 1);
lean_closure_set(v___f_1224_, 0, v___x_1223_);
v___x_1225_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1226_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1225_, v___f_1224_, v___y_1209_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1236_; 
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1226_, 0);
lean_dec(v_unused_1237_);
v___x_1228_ = v___x_1226_;
v_isShared_1229_ = v_isSharedCheck_1236_;
goto v_resetjp_1227_;
}
else
{
lean_dec(v___x_1226_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1236_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1221_);
v___x_1231_ = v___x_1200_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1221_);
v___x_1231_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1231_);
v___x_1233_ = v___x_1228_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
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
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_del_object(v___x_1200_);
v_a_1238_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1226_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1226_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec(v_a_1215_);
lean_dec_ref(v___x_1206_);
lean_del_object(v___x_1200_);
lean_dec(v_val_1198_);
lean_dec(v_val_1185_);
lean_dec_ref(v_type_1172_);
v_a_1246_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1216_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1216_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v___x_1206_);
lean_del_object(v___x_1200_);
lean_dec(v_val_1198_);
lean_dec(v_val_1185_);
lean_dec_ref(v_type_1172_);
v_a_1254_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1214_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1214_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
lean_dec(v_a_1192_);
lean_dec_ref_known(v___x_1188_, 2);
lean_dec(v_val_1185_);
lean_dec_ref(v_type_1172_);
v___x_1278_ = lean_box(0);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1278_);
v___x_1280_ = v___x_1194_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
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
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec_ref_known(v___x_1188_, 2);
lean_dec(v_val_1185_);
lean_dec_ref(v_type_1172_);
v_a_1283_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1191_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1191_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec(v_a_1181_);
lean_dec_ref(v_type_1172_);
v___x_1291_ = lean_box(0);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1291_);
v___x_1293_ = v___x_1183_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v_type_1172_);
v_a_1296_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1180_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1180_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(lean_object* v_type_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
lean_object* v_ks_1317_; lean_object* v_vs_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1344_; 
v_ks_1317_ = lean_ctor_get(v_x_1313_, 0);
v_vs_1318_ = lean_ctor_get(v_x_1313_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_x_1313_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1320_ = v_x_1313_;
v_isShared_1321_ = v_isSharedCheck_1344_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_vs_1318_);
lean_inc(v_ks_1317_);
lean_dec(v_x_1313_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1344_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_array_get_size(v_ks_1317_);
v___x_1323_ = lean_nat_dec_lt(v_x_1314_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_dec(v_x_1314_);
v___x_1324_ = lean_array_push(v_ks_1317_, v_x_1315_);
v___x_1325_ = lean_array_push(v_vs_1318_, v_x_1316_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 1, v___x_1325_);
lean_ctor_set(v___x_1320_, 0, v___x_1324_);
v___x_1327_ = v___x_1320_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
else
{
lean_object* v_k_x27_1329_; size_t v___x_1330_; size_t v___x_1331_; uint8_t v___x_1332_; 
v_k_x27_1329_ = lean_array_fget_borrowed(v_ks_1317_, v_x_1314_);
v___x_1330_ = lean_ptr_addr(v_x_1315_);
v___x_1331_ = lean_ptr_addr(v_k_x27_1329_);
v___x_1332_ = lean_usize_dec_eq(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1334_; 
if (v_isShared_1321_ == 0)
{
v___x_1334_ = v___x_1320_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_ks_1317_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_vs_1318_);
v___x_1334_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = lean_unsigned_to_nat(1u);
v___x_1336_ = lean_nat_add(v_x_1314_, v___x_1335_);
lean_dec(v_x_1314_);
v_x_1313_ = v___x_1334_;
v_x_1314_ = v___x_1336_;
goto _start;
}
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1339_ = lean_array_fset(v_ks_1317_, v_x_1314_, v_x_1315_);
v___x_1340_ = lean_array_fset(v_vs_1318_, v_x_1314_, v_x_1316_);
lean_dec(v_x_1314_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 1, v___x_1340_);
lean_ctor_set(v___x_1320_, 0, v___x_1339_);
v___x_1342_ = v___x_1320_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1345_, lean_object* v_k_1346_, lean_object* v_v_1347_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1345_, v___x_1348_, v_k_1346_, v_v_1347_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(lean_object* v_x_1351_, size_t v_x_1352_, size_t v_x_1353_, lean_object* v_x_1354_, lean_object* v_x_1355_){
_start:
{
if (lean_obj_tag(v_x_1351_) == 0)
{
lean_object* v_es_1356_; size_t v___x_1357_; size_t v___x_1358_; lean_object* v_j_1359_; lean_object* v___x_1360_; uint8_t v___x_1361_; 
v_es_1356_ = lean_ctor_get(v_x_1351_, 0);
v___x_1357_ = ((size_t)31ULL);
v___x_1358_ = lean_usize_land(v_x_1352_, v___x_1357_);
v_j_1359_ = lean_usize_to_nat(v___x_1358_);
v___x_1360_ = lean_array_get_size(v_es_1356_);
v___x_1361_ = lean_nat_dec_lt(v_j_1359_, v___x_1360_);
if (v___x_1361_ == 0)
{
lean_dec(v_j_1359_);
lean_dec(v_x_1355_);
lean_dec_ref(v_x_1354_);
return v_x_1351_;
}
else
{
lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1402_; 
lean_inc_ref(v_es_1356_);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v_x_1351_, 0);
lean_dec(v_unused_1403_);
v___x_1363_ = v_x_1351_;
v_isShared_1364_ = v_isSharedCheck_1402_;
goto v_resetjp_1362_;
}
else
{
lean_dec(v_x_1351_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1402_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v_v_1365_; lean_object* v___x_1366_; lean_object* v_xs_x27_1367_; lean_object* v___y_1369_; 
v_v_1365_ = lean_array_fget(v_es_1356_, v_j_1359_);
v___x_1366_ = lean_box(0);
v_xs_x27_1367_ = lean_array_fset(v_es_1356_, v_j_1359_, v___x_1366_);
switch(lean_obj_tag(v_v_1365_))
{
case 0:
{
lean_object* v_key_1374_; lean_object* v_val_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1387_; 
v_key_1374_ = lean_ctor_get(v_v_1365_, 0);
v_val_1375_ = lean_ctor_get(v_v_1365_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_v_1365_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1377_ = v_v_1365_;
v_isShared_1378_ = v_isSharedCheck_1387_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_val_1375_);
lean_inc(v_key_1374_);
lean_dec(v_v_1365_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1387_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
size_t v___x_1379_; size_t v___x_1380_; uint8_t v___x_1381_; 
v___x_1379_ = lean_ptr_addr(v_x_1354_);
v___x_1380_ = lean_ptr_addr(v_key_1374_);
v___x_1381_ = lean_usize_dec_eq(v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_del_object(v___x_1377_);
v___x_1382_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1374_, v_val_1375_, v_x_1354_, v_x_1355_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
v___y_1369_ = v___x_1383_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1385_; 
lean_dec(v_val_1375_);
lean_dec(v_key_1374_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v_x_1355_);
lean_ctor_set(v___x_1377_, 0, v_x_1354_);
v___x_1385_ = v___x_1377_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_x_1354_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_x_1355_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
v___y_1369_ = v___x_1385_;
goto v___jp_1368_;
}
}
}
}
case 1:
{
lean_object* v_node_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1400_; 
v_node_1388_ = lean_ctor_get(v_v_1365_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_v_1365_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1390_ = v_v_1365_;
v_isShared_1391_ = v_isSharedCheck_1400_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_node_1388_);
lean_dec(v_v_1365_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1400_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
size_t v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1392_ = ((size_t)5ULL);
v___x_1393_ = lean_usize_shift_right(v_x_1352_, v___x_1392_);
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = lean_usize_add(v_x_1353_, v___x_1394_);
v___x_1396_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_node_1388_, v___x_1393_, v___x_1395_, v_x_1354_, v_x_1355_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1396_);
v___x_1398_ = v___x_1390_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
v___y_1369_ = v___x_1398_;
goto v___jp_1368_;
}
}
}
default: 
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_x_1354_);
lean_ctor_set(v___x_1401_, 1, v_x_1355_);
v___y_1369_ = v___x_1401_;
goto v___jp_1368_;
}
}
v___jp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_array_fset(v_xs_x27_1367_, v_j_1359_, v___y_1369_);
lean_dec(v_j_1359_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1370_);
v___x_1372_ = v___x_1363_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
else
{
lean_object* v_ks_1404_; lean_object* v_vs_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1423_; 
v_ks_1404_ = lean_ctor_get(v_x_1351_, 0);
v_vs_1405_ = lean_ctor_get(v_x_1351_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_x_1351_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1407_ = v_x_1351_;
v_isShared_1408_ = v_isSharedCheck_1423_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_vs_1405_);
lean_inc(v_ks_1404_);
lean_dec(v_x_1351_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1423_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_ks_1404_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_vs_1405_);
v___x_1410_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v_newNode_1411_; size_t v___x_1412_; uint8_t v___x_1413_; 
v_newNode_1411_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v___x_1410_, v_x_1354_, v_x_1355_);
v___x_1412_ = ((size_t)7ULL);
v___x_1413_ = lean_usize_dec_le(v___x_1412_, v_x_1353_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1414_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1411_);
v___x_1415_ = lean_unsigned_to_nat(4u);
v___x_1416_ = lean_nat_dec_lt(v___x_1414_, v___x_1415_);
lean_dec(v___x_1414_);
if (v___x_1416_ == 0)
{
lean_object* v_ks_1417_; lean_object* v_vs_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_ks_1417_ = lean_ctor_get(v_newNode_1411_, 0);
lean_inc_ref(v_ks_1417_);
v_vs_1418_ = lean_ctor_get(v_newNode_1411_, 1);
lean_inc_ref(v_vs_1418_);
lean_dec_ref(v_newNode_1411_);
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0);
v___x_1421_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_x_1353_, v_ks_1417_, v_vs_1418_, v___x_1419_, v___x_1420_);
lean_dec_ref(v_vs_1418_);
lean_dec_ref(v_ks_1417_);
return v___x_1421_;
}
else
{
return v_newNode_1411_;
}
}
else
{
return v_newNode_1411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(size_t v_depth_1424_, lean_object* v_keys_1425_, lean_object* v_vals_1426_, lean_object* v_i_1427_, lean_object* v_entries_1428_){
_start:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_array_get_size(v_keys_1425_);
v___x_1430_ = lean_nat_dec_lt(v_i_1427_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_dec(v_i_1427_);
return v_entries_1428_;
}
else
{
lean_object* v_k_1431_; lean_object* v_v_1432_; size_t v___x_1433_; size_t v___x_1434_; size_t v___x_1435_; uint64_t v___x_1436_; size_t v_h_1437_; size_t v___x_1438_; lean_object* v___x_1439_; size_t v___x_1440_; size_t v___x_1441_; size_t v___x_1442_; size_t v_h_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v_k_1431_ = lean_array_fget_borrowed(v_keys_1425_, v_i_1427_);
v_v_1432_ = lean_array_fget_borrowed(v_vals_1426_, v_i_1427_);
v___x_1433_ = lean_ptr_addr(v_k_1431_);
v___x_1434_ = ((size_t)3ULL);
v___x_1435_ = lean_usize_shift_right(v___x_1433_, v___x_1434_);
v___x_1436_ = lean_usize_to_uint64(v___x_1435_);
v_h_1437_ = lean_uint64_to_usize(v___x_1436_);
v___x_1438_ = ((size_t)5ULL);
v___x_1439_ = lean_unsigned_to_nat(1u);
v___x_1440_ = ((size_t)1ULL);
v___x_1441_ = lean_usize_sub(v_depth_1424_, v___x_1440_);
v___x_1442_ = lean_usize_mul(v___x_1438_, v___x_1441_);
v_h_1443_ = lean_usize_shift_right(v_h_1437_, v___x_1442_);
v___x_1444_ = lean_nat_add(v_i_1427_, v___x_1439_);
lean_dec(v_i_1427_);
lean_inc(v_v_1432_);
lean_inc(v_k_1431_);
v___x_1445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_entries_1428_, v_h_1443_, v_depth_1424_, v_k_1431_, v_v_1432_);
v_i_1427_ = v___x_1444_;
v_entries_1428_ = v___x_1445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1447_, lean_object* v_keys_1448_, lean_object* v_vals_1449_, lean_object* v_i_1450_, lean_object* v_entries_1451_){
_start:
{
size_t v_depth_boxed_1452_; lean_object* v_res_1453_; 
v_depth_boxed_1452_ = lean_unbox_usize(v_depth_1447_);
lean_dec(v_depth_1447_);
v_res_1453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1452_, v_keys_1448_, v_vals_1449_, v_i_1450_, v_entries_1451_);
lean_dec_ref(v_vals_1449_);
lean_dec_ref(v_keys_1448_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_x_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_){
_start:
{
size_t v_x_2146__boxed_1459_; size_t v_x_2147__boxed_1460_; lean_object* v_res_1461_; 
v_x_2146__boxed_1459_ = lean_unbox_usize(v_x_1455_);
lean_dec(v_x_1455_);
v_x_2147__boxed_1460_ = lean_unbox_usize(v_x_1456_);
lean_dec(v_x_1456_);
v_res_1461_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1454_, v_x_2146__boxed_1459_, v_x_2147__boxed_1460_, v_x_1457_, v_x_1458_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
size_t v___x_1465_; size_t v___x_1466_; size_t v___x_1467_; uint64_t v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1465_ = lean_ptr_addr(v_x_1463_);
v___x_1466_ = ((size_t)3ULL);
v___x_1467_ = lean_usize_shift_right(v___x_1465_, v___x_1466_);
v___x_1468_ = lean_usize_to_uint64(v___x_1467_);
v___x_1469_ = lean_uint64_to_usize(v___x_1468_);
v___x_1470_ = ((size_t)1ULL);
v___x_1471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1462_, v___x_1469_, v___x_1470_, v_x_1463_, v_x_1464_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(lean_object* v_type_1472_, lean_object* v___y_1473_, lean_object* v_s_1474_){
_start:
{
lean_object* v_exp_1475_; lean_object* v_rings_1476_; lean_object* v_semirings_1477_; lean_object* v_ncRings_1478_; lean_object* v_ncSemirings_1479_; lean_object* v_typeClassify_1480_; lean_object* v_orders_1481_; lean_object* v_typeOrderClassify_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1490_; 
v_exp_1475_ = lean_ctor_get(v_s_1474_, 0);
v_rings_1476_ = lean_ctor_get(v_s_1474_, 1);
v_semirings_1477_ = lean_ctor_get(v_s_1474_, 2);
v_ncRings_1478_ = lean_ctor_get(v_s_1474_, 3);
v_ncSemirings_1479_ = lean_ctor_get(v_s_1474_, 4);
v_typeClassify_1480_ = lean_ctor_get(v_s_1474_, 5);
v_orders_1481_ = lean_ctor_get(v_s_1474_, 6);
v_typeOrderClassify_1482_ = lean_ctor_get(v_s_1474_, 7);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_s_1474_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1484_ = v_s_1474_;
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_typeOrderClassify_1482_);
lean_inc(v_orders_1481_);
lean_inc(v_typeClassify_1480_);
lean_inc(v_ncSemirings_1479_);
lean_inc(v_ncRings_1478_);
lean_inc(v_semirings_1477_);
lean_inc(v_rings_1476_);
lean_inc(v_exp_1475_);
lean_dec(v_s_1474_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1490_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_1480_, v_type_1472_, v___y_1473_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 5, v___x_1486_);
v___x_1488_ = v___x_1484_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_exp_1475_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_rings_1476_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_semirings_1477_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_ncRings_1478_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_ncSemirings_1479_);
lean_ctor_set(v_reuseFailAlloc_1489_, 5, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1489_, 6, v_orders_1481_);
lean_ctor_set(v_reuseFailAlloc_1489_, 7, v_typeOrderClassify_1482_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1491_, lean_object* v_vals_1492_, lean_object* v_i_1493_, lean_object* v_k_1494_){
_start:
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = lean_array_get_size(v_keys_1491_);
v___x_1496_ = lean_nat_dec_lt(v_i_1493_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
lean_dec(v_i_1493_);
v___x_1497_ = lean_box(0);
return v___x_1497_;
}
else
{
lean_object* v_k_x27_1498_; size_t v___x_1499_; size_t v___x_1500_; uint8_t v___x_1501_; 
v_k_x27_1498_ = lean_array_fget_borrowed(v_keys_1491_, v_i_1493_);
v___x_1499_ = lean_ptr_addr(v_k_1494_);
v___x_1500_ = lean_ptr_addr(v_k_x27_1498_);
v___x_1501_ = lean_usize_dec_eq(v___x_1499_, v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_nat_add(v_i_1493_, v___x_1502_);
lean_dec(v_i_1493_);
v_i_1493_ = v___x_1503_;
goto _start;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_array_fget_borrowed(v_vals_1492_, v_i_1493_);
lean_dec(v_i_1493_);
lean_inc(v___x_1505_);
v___x_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1507_, lean_object* v_vals_1508_, lean_object* v_i_1509_, lean_object* v_k_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1507_, v_vals_1508_, v_i_1509_, v_k_1510_);
lean_dec_ref(v_k_1510_);
lean_dec_ref(v_vals_1508_);
lean_dec_ref(v_keys_1507_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(lean_object* v_x_1512_, size_t v_x_1513_, lean_object* v_x_1514_){
_start:
{
if (lean_obj_tag(v_x_1512_) == 0)
{
lean_object* v_es_1515_; lean_object* v___x_1516_; size_t v___x_1517_; size_t v___x_1518_; lean_object* v_j_1519_; lean_object* v___x_1520_; 
v_es_1515_ = lean_ctor_get(v_x_1512_, 0);
v___x_1516_ = lean_box(2);
v___x_1517_ = ((size_t)31ULL);
v___x_1518_ = lean_usize_land(v_x_1513_, v___x_1517_);
v_j_1519_ = lean_usize_to_nat(v___x_1518_);
v___x_1520_ = lean_array_get_borrowed(v___x_1516_, v_es_1515_, v_j_1519_);
lean_dec(v_j_1519_);
switch(lean_obj_tag(v___x_1520_))
{
case 0:
{
lean_object* v_key_1521_; lean_object* v_val_1522_; size_t v___x_1523_; size_t v___x_1524_; uint8_t v___x_1525_; 
v_key_1521_ = lean_ctor_get(v___x_1520_, 0);
v_val_1522_ = lean_ctor_get(v___x_1520_, 1);
v___x_1523_ = lean_ptr_addr(v_x_1514_);
v___x_1524_ = lean_ptr_addr(v_key_1521_);
v___x_1525_ = lean_usize_dec_eq(v___x_1523_, v___x_1524_);
if (v___x_1525_ == 0)
{
lean_object* v___x_1526_; 
v___x_1526_ = lean_box(0);
return v___x_1526_;
}
else
{
lean_object* v___x_1527_; 
lean_inc(v_val_1522_);
v___x_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_val_1522_);
return v___x_1527_;
}
}
case 1:
{
lean_object* v_node_1528_; size_t v___x_1529_; size_t v___x_1530_; 
v_node_1528_ = lean_ctor_get(v___x_1520_, 0);
v___x_1529_ = ((size_t)5ULL);
v___x_1530_ = lean_usize_shift_right(v_x_1513_, v___x_1529_);
v_x_1512_ = v_node_1528_;
v_x_1513_ = v___x_1530_;
goto _start;
}
default: 
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_box(0);
return v___x_1532_;
}
}
}
else
{
lean_object* v_ks_1533_; lean_object* v_vs_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_ks_1533_ = lean_ctor_get(v_x_1512_, 0);
v_vs_1534_ = lean_ctor_get(v_x_1512_, 1);
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1533_, v_vs_1534_, v___x_1535_, v_x_1514_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
size_t v_x_2365__boxed_1540_; lean_object* v_res_1541_; 
v_x_2365__boxed_1540_ = lean_unbox_usize(v_x_1538_);
lean_dec(v_x_1538_);
v_res_1541_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1537_, v_x_2365__boxed_1540_, v_x_1539_);
lean_dec_ref(v_x_1539_);
lean_dec_ref(v_x_1537_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(lean_object* v_x_1542_, lean_object* v_x_1543_){
_start:
{
size_t v___x_1544_; size_t v___x_1545_; size_t v___x_1546_; uint64_t v___x_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
v___x_1544_ = lean_ptr_addr(v_x_1543_);
v___x_1545_ = ((size_t)3ULL);
v___x_1546_ = lean_usize_shift_right(v___x_1544_, v___x_1545_);
v___x_1547_ = lean_usize_to_uint64(v___x_1546_);
v___x_1548_ = lean_uint64_to_usize(v___x_1547_);
v___x_1549_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1542_, v___x_1548_, v_x_1543_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(lean_object* v_x_1550_, lean_object* v_x_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_1550_, v_x_1551_);
lean_dec_ref(v_x_1551_);
lean_dec_ref(v_x_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(lean_object* v_type_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1555_, v_a_1558_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1616_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1616_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1616_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_typeClassify_1566_; lean_object* v___x_1567_; 
v_typeClassify_1566_ = lean_ctor_get(v_a_1562_, 5);
lean_inc_ref(v_typeClassify_1566_);
lean_dec(v_a_1562_);
v___x_1567_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_1566_, v_type_1553_);
lean_dec_ref(v_typeClassify_1566_);
if (lean_obj_tag(v___x_1567_) == 1)
{
lean_object* v_val_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1583_; 
lean_dec_ref(v_type_1553_);
v_val_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1583_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_val_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1583_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
if (lean_obj_tag(v_val_1568_) == 0)
{
lean_object* v_id_1572_; lean_object* v___x_1574_; 
v_id_1572_ = lean_ctor_get(v_val_1568_, 0);
lean_inc(v_id_1572_);
lean_dec_ref_known(v_val_1568_, 1);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_id_1572_);
v___x_1574_ = v___x_1570_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_id_1572_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1574_);
v___x_1576_ = v___x_1564_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_del_object(v___x_1570_);
lean_dec(v_val_1568_);
v___x_1579_ = lean_box(0);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1579_);
v___x_1581_ = v___x_1564_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_object* v___x_1584_; 
lean_dec(v___x_1567_);
lean_del_object(v___x_1564_);
lean_inc_ref(v_type_1553_);
v___x_1584_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1615_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1615_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1615_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___y_1590_; 
if (lean_obj_tag(v_a_1585_) == 0)
{
lean_object* v___x_1610_; 
lean_del_object(v___x_1587_);
v___x_1610_ = lean_box(4);
v___y_1590_ = v___x_1610_;
goto v___jp_1589_;
}
else
{
lean_object* v_val_1611_; lean_object* v___x_1613_; 
v_val_1611_ = lean_ctor_get(v_a_1585_, 0);
lean_inc(v_val_1611_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_val_1611_);
v___x_1613_ = v___x_1587_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_val_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
v___y_1590_ = v___x_1613_;
goto v___jp_1589_;
}
}
v___jp_1589_:
{
lean_object* v___f_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___f_1591_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0), 3, 2);
lean_closure_set(v___f_1591_, 0, v_type_1553_);
lean_closure_set(v___f_1591_, 1, v___y_1590_);
v___x_1592_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1593_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1592_, v___f_1591_, v_a_1555_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v___x_1593_, 0);
lean_dec(v_unused_1601_);
v___x_1595_ = v___x_1593_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v___x_1593_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_a_1585_);
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1585_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_a_1585_);
v_a_1602_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1593_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1593_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
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
}
else
{
lean_dec_ref(v_type_1553_);
return v___x_1584_;
}
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec_ref(v_type_1553_);
v_a_1617_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1561_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1561_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(lean_object* v_type_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_type_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(lean_object* v_00_u03b2_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_1635_, v_x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(lean_object* v_00_u03b2_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(v_00_u03b2_1638_, v_x_1639_, v_x_1640_);
lean_dec_ref(v_x_1640_);
lean_dec_ref(v_x_1639_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(lean_object* v_00_u03b2_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_x_1643_, v_x_1644_, v_x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1647_, lean_object* v_x_1648_, size_t v_x_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_1648_, v_x_1649_, v_x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
size_t v_x_2581__boxed_1656_; lean_object* v_res_1657_; 
v_x_2581__boxed_1656_ = lean_unbox_usize(v_x_1654_);
lean_dec(v_x_1654_);
v_res_1657_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(v_00_u03b2_1652_, v_x_1653_, v_x_2581__boxed_1656_, v_x_1655_);
lean_dec_ref(v_x_1655_);
lean_dec_ref(v_x_1653_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(lean_object* v_00_u03b2_1658_, lean_object* v_x_1659_, size_t v_x_1660_, size_t v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_1659_, v_x_1660_, v_x_1661_, v_x_1662_, v_x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_){
_start:
{
size_t v_x_2592__boxed_1671_; size_t v_x_2593__boxed_1672_; lean_object* v_res_1673_; 
v_x_2592__boxed_1671_ = lean_unbox_usize(v_x_1667_);
lean_dec(v_x_1667_);
v_x_2593__boxed_1672_ = lean_unbox_usize(v_x_1668_);
lean_dec(v_x_1668_);
v_res_1673_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(v_00_u03b2_1665_, v_x_1666_, v_x_2592__boxed_1671_, v_x_2593__boxed_1672_, v_x_1669_, v_x_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1674_, lean_object* v_keys_1675_, lean_object* v_vals_1676_, lean_object* v_heq_1677_, lean_object* v_i_1678_, lean_object* v_k_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1675_, v_vals_1676_, v_i_1678_, v_k_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1681_, lean_object* v_keys_1682_, lean_object* v_vals_1683_, lean_object* v_heq_1684_, lean_object* v_i_1685_, lean_object* v_k_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1681_, v_keys_1682_, v_vals_1683_, v_heq_1684_, v_i_1685_, v_k_1686_);
lean_dec_ref(v_k_1686_);
lean_dec_ref(v_vals_1683_);
lean_dec_ref(v_keys_1682_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1688_, lean_object* v_n_1689_, lean_object* v_k_1690_, lean_object* v_v_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v_n_1689_, v_k_1690_, v_v_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1693_, size_t v_depth_1694_, lean_object* v_keys_1695_, lean_object* v_vals_1696_, lean_object* v_heq_1697_, lean_object* v_i_1698_, lean_object* v_entries_1699_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1694_, v_keys_1695_, v_vals_1696_, v_i_1698_, v_entries_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1701_, lean_object* v_depth_1702_, lean_object* v_keys_1703_, lean_object* v_vals_1704_, lean_object* v_heq_1705_, lean_object* v_i_1706_, lean_object* v_entries_1707_){
_start:
{
size_t v_depth_boxed_1708_; lean_object* v_res_1709_; 
v_depth_boxed_1708_ = lean_unbox_usize(v_depth_1702_);
lean_dec(v_depth_1702_);
v_res_1709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1701_, v_depth_boxed_1708_, v_keys_1703_, v_vals_1704_, v_heq_1705_, v_i_1706_, v_entries_1707_);
lean_dec_ref(v_vals_1704_);
lean_dec_ref(v_keys_1703_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1710_, lean_object* v_x_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1711_, v_x_1712_, v_x_1713_, v_x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(lean_object* v_val_1716_, lean_object* v___x_1717_, lean_object* v_s_1718_){
_start:
{
lean_object* v_exp_1719_; lean_object* v_rings_1720_; lean_object* v_semirings_1721_; lean_object* v_ncRings_1722_; lean_object* v_ncSemirings_1723_; lean_object* v_typeClassify_1724_; lean_object* v_orders_1725_; lean_object* v_typeOrderClassify_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; 
v_exp_1719_ = lean_ctor_get(v_s_1718_, 0);
v_rings_1720_ = lean_ctor_get(v_s_1718_, 1);
v_semirings_1721_ = lean_ctor_get(v_s_1718_, 2);
v_ncRings_1722_ = lean_ctor_get(v_s_1718_, 3);
v_ncSemirings_1723_ = lean_ctor_get(v_s_1718_, 4);
v_typeClassify_1724_ = lean_ctor_get(v_s_1718_, 5);
v_orders_1725_ = lean_ctor_get(v_s_1718_, 6);
v_typeOrderClassify_1726_ = lean_ctor_get(v_s_1718_, 7);
v___x_1727_ = lean_array_get_size(v_rings_1720_);
v___x_1728_ = lean_nat_dec_lt(v_val_1716_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_dec(v___x_1717_);
return v_s_1718_;
}
else
{
lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1756_; 
lean_inc_ref(v_typeOrderClassify_1726_);
lean_inc_ref(v_orders_1725_);
lean_inc_ref(v_typeClassify_1724_);
lean_inc_ref(v_ncSemirings_1723_);
lean_inc_ref(v_ncRings_1722_);
lean_inc_ref(v_semirings_1721_);
lean_inc_ref(v_rings_1720_);
lean_inc(v_exp_1719_);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_s_1718_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; lean_object* v_unused_1758_; lean_object* v_unused_1759_; lean_object* v_unused_1760_; lean_object* v_unused_1761_; lean_object* v_unused_1762_; lean_object* v_unused_1763_; lean_object* v_unused_1764_; 
v_unused_1757_ = lean_ctor_get(v_s_1718_, 7);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_s_1718_, 6);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v_s_1718_, 5);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_s_1718_, 4);
lean_dec(v_unused_1760_);
v_unused_1761_ = lean_ctor_get(v_s_1718_, 3);
lean_dec(v_unused_1761_);
v_unused_1762_ = lean_ctor_get(v_s_1718_, 2);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_s_1718_, 1);
lean_dec(v_unused_1763_);
v_unused_1764_ = lean_ctor_get(v_s_1718_, 0);
lean_dec(v_unused_1764_);
v___x_1730_ = v_s_1718_;
v_isShared_1731_ = v_isSharedCheck_1756_;
goto v_resetjp_1729_;
}
else
{
lean_dec(v_s_1718_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1756_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_v_1732_; lean_object* v_toRing_1733_; lean_object* v_invFn_x3f_1734_; lean_object* v_divFn_x3f_1735_; lean_object* v_commSemiringInst_1736_; lean_object* v_commRingInst_1737_; lean_object* v_noZeroDivInst_x3f_1738_; lean_object* v_fieldInst_x3f_1739_; lean_object* v_powIdentityInst_x3f_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1754_; 
v_v_1732_ = lean_array_fget(v_rings_1720_, v_val_1716_);
v_toRing_1733_ = lean_ctor_get(v_v_1732_, 0);
v_invFn_x3f_1734_ = lean_ctor_get(v_v_1732_, 1);
v_divFn_x3f_1735_ = lean_ctor_get(v_v_1732_, 2);
v_commSemiringInst_1736_ = lean_ctor_get(v_v_1732_, 4);
v_commRingInst_1737_ = lean_ctor_get(v_v_1732_, 5);
v_noZeroDivInst_x3f_1738_ = lean_ctor_get(v_v_1732_, 6);
v_fieldInst_x3f_1739_ = lean_ctor_get(v_v_1732_, 7);
v_powIdentityInst_x3f_1740_ = lean_ctor_get(v_v_1732_, 8);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_v_1732_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v_v_1732_, 3);
lean_dec(v_unused_1755_);
v___x_1742_ = v_v_1732_;
v_isShared_1743_ = v_isSharedCheck_1754_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1740_);
lean_inc(v_fieldInst_x3f_1739_);
lean_inc(v_noZeroDivInst_x3f_1738_);
lean_inc(v_commRingInst_1737_);
lean_inc(v_commSemiringInst_1736_);
lean_inc(v_divFn_x3f_1735_);
lean_inc(v_invFn_x3f_1734_);
lean_inc(v_toRing_1733_);
lean_dec(v_v_1732_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1754_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v_xs_x27_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1744_ = lean_box(0);
v_xs_x27_1745_ = lean_array_fset(v_rings_1720_, v_val_1716_, v___x_1744_);
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1717_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 3, v___x_1746_);
v___x_1748_ = v___x_1742_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_toRing_1733_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_invFn_x3f_1734_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_divFn_x3f_1735_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_commSemiringInst_1736_);
lean_ctor_set(v_reuseFailAlloc_1753_, 5, v_commRingInst_1737_);
lean_ctor_set(v_reuseFailAlloc_1753_, 6, v_noZeroDivInst_x3f_1738_);
lean_ctor_set(v_reuseFailAlloc_1753_, 7, v_fieldInst_x3f_1739_);
lean_ctor_set(v_reuseFailAlloc_1753_, 8, v_powIdentityInst_x3f_1740_);
v___x_1748_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1749_ = lean_array_fset(v_xs_x27_1745_, v_val_1716_, v___x_1748_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v___x_1749_);
v___x_1751_ = v___x_1730_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_exp_1719_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_semirings_1721_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_ncRings_1722_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_ncSemirings_1723_);
lean_ctor_set(v_reuseFailAlloc_1752_, 5, v_typeClassify_1724_);
lean_ctor_set(v_reuseFailAlloc_1752_, 6, v_orders_1725_);
lean_ctor_set(v_reuseFailAlloc_1752_, 7, v_typeOrderClassify_1726_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed(lean_object* v_val_1765_, lean_object* v___x_1766_, lean_object* v_s_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(v_val_1765_, v___x_1766_, v_s_1767_);
lean_dec(v_val_1765_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(lean_object* v___x_1769_, lean_object* v_s_1770_){
_start:
{
lean_object* v_exp_1771_; lean_object* v_rings_1772_; lean_object* v_semirings_1773_; lean_object* v_ncRings_1774_; lean_object* v_ncSemirings_1775_; lean_object* v_typeClassify_1776_; lean_object* v_orders_1777_; lean_object* v_typeOrderClassify_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1786_; 
v_exp_1771_ = lean_ctor_get(v_s_1770_, 0);
v_rings_1772_ = lean_ctor_get(v_s_1770_, 1);
v_semirings_1773_ = lean_ctor_get(v_s_1770_, 2);
v_ncRings_1774_ = lean_ctor_get(v_s_1770_, 3);
v_ncSemirings_1775_ = lean_ctor_get(v_s_1770_, 4);
v_typeClassify_1776_ = lean_ctor_get(v_s_1770_, 5);
v_orders_1777_ = lean_ctor_get(v_s_1770_, 6);
v_typeOrderClassify_1778_ = lean_ctor_get(v_s_1770_, 7);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_s_1770_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1780_ = v_s_1770_;
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_typeOrderClassify_1778_);
lean_inc(v_orders_1777_);
lean_inc(v_typeClassify_1776_);
lean_inc(v_ncSemirings_1775_);
lean_inc(v_ncRings_1774_);
lean_inc(v_semirings_1773_);
lean_inc(v_rings_1772_);
lean_inc(v_exp_1771_);
lean_dec(v_s_1770_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1786_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1784_; 
v___x_1782_ = lean_array_push(v_semirings_1773_, v___x_1769_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 2, v___x_1782_);
v___x_1784_ = v___x_1780_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_exp_1771_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_rings_1772_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_ncRings_1774_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v_ncSemirings_1775_);
lean_ctor_set(v_reuseFailAlloc_1785_, 5, v_typeClassify_1776_);
lean_ctor_set(v_reuseFailAlloc_1785_, 6, v_orders_1777_);
lean_ctor_set(v_reuseFailAlloc_1785_, 7, v_typeOrderClassify_1778_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(lean_object* v_type_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1801_; 
lean_inc_ref(v_type_1790_);
v___x_1801_ = l_Lean_Meta_getDecLevel_x3f(v_type_1790_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1939_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1939_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1939_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
if (lean_obj_tag(v_a_1802_) == 1)
{
lean_object* v_val_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_del_object(v___x_1804_);
v_val_1806_ = lean_ctor_get(v_a_1802_, 0);
lean_inc_n(v_val_1806_, 2);
lean_dec_ref_known(v_a_1802_, 1);
v___x_1807_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__18));
v___x_1808_ = lean_box(0);
v___x_1809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1809_, 0, v_val_1806_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
lean_inc_ref(v___x_1809_);
v___x_1810_ = l_Lean_mkConst(v___x_1807_, v___x_1809_);
lean_inc_ref(v_type_1790_);
v___x_1811_ = l_Lean_Expr_app___override(v___x_1810_, v_type_1790_);
v___x_1812_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1811_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1926_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1926_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1926_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
if (lean_obj_tag(v_a_1813_) == 1)
{
lean_object* v_val_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_del_object(v___x_1815_);
v_val_1817_ = lean_ctor_get(v_a_1813_, 0);
lean_inc_n(v_val_1817_, 2);
lean_dec_ref_known(v_a_1813_, 1);
v___x_1818_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2));
lean_inc_ref(v___x_1809_);
v___x_1819_ = l_Lean_mkConst(v___x_1818_, v___x_1809_);
lean_inc_ref_n(v_type_1790_, 2);
v___x_1820_ = l_Lean_mkAppB(v___x_1819_, v_type_1790_, v_val_1817_);
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1));
v___x_1822_ = l_Lean_mkConst(v___x_1821_, v___x_1809_);
lean_inc_ref(v___x_1820_);
v___x_1823_ = l_Lean_mkAppB(v___x_1822_, v_type_1790_, v___x_1820_);
v___x_1824_ = l_Lean_Meta_Sym_canon(v___x_1823_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1826_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___x_1826_ = l_Lean_Meta_Sym_shareCommon(v_a_1825_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc_n(v_a_1827_, 2);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_a_1827_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
if (lean_obj_tag(v_a_1829_) == 1)
{
lean_object* v_val_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v_a_1827_);
v_val_1830_ = lean_ctor_get(v_a_1829_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_a_1829_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1832_ = v_a_1829_;
v_isShared_1833_ = v_isSharedCheck_1882_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_val_1830_);
lean_dec(v_a_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1882_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1792_, v_a_1795_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v_semirings_1836_; lean_object* v___x_1837_; lean_object* v___f_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v_semirings_1836_ = lean_ctor_get(v_a_1835_, 2);
lean_inc_ref(v_semirings_1836_);
lean_dec(v_a_1835_);
v___x_1837_ = lean_array_get_size(v_semirings_1836_);
lean_dec_ref(v_semirings_1836_);
lean_inc(v_val_1830_);
v___f_1838_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1838_, 0, v_val_1830_);
lean_closure_set(v___f_1838_, 1, v___x_1837_);
v___x_1839_ = lean_box(0);
v___x_1840_ = 0;
v___x_1841_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1841_, 0, v___x_1837_);
lean_ctor_set(v___x_1841_, 1, v_type_1790_);
lean_ctor_set(v___x_1841_, 2, v_val_1806_);
lean_ctor_set(v___x_1841_, 3, v___x_1820_);
lean_ctor_set(v___x_1841_, 4, v___x_1839_);
lean_ctor_set(v___x_1841_, 5, v___x_1839_);
lean_ctor_set(v___x_1841_, 6, v___x_1839_);
lean_ctor_set(v___x_1841_, 7, v___x_1839_);
lean_ctor_set(v___x_1841_, 8, v___x_1839_);
lean_ctor_set(v___x_1841_, 9, v___x_1839_);
lean_ctor_set_uint8(v___x_1841_, sizeof(void*)*10, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v_val_1830_);
lean_ctor_set(v___x_1842_, 2, v_val_1817_);
lean_ctor_set(v___x_1842_, 3, v___x_1839_);
lean_ctor_set(v___x_1842_, 4, v___x_1839_);
v___f_1843_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1), 2, 1);
lean_closure_set(v___f_1843_, 0, v___x_1842_);
v___x_1844_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_1845_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1844_, v___f_1843_, v_a_1792_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref_known(v___x_1845_, 1);
v___x_1846_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_1844_, v___f_1838_, v_a_1792_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1856_; 
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v___x_1846_, 0);
lean_dec(v_unused_1857_);
v___x_1848_ = v___x_1846_;
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
else
{
lean_dec(v___x_1846_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1856_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1837_);
v___x_1851_ = v___x_1832_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1837_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1851_);
v___x_1853_ = v___x_1848_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_del_object(v___x_1832_);
v_a_1858_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1846_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1846_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v___f_1838_);
lean_del_object(v___x_1832_);
v_a_1866_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1845_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1845_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1832_);
lean_dec(v_val_1830_);
lean_dec_ref(v___x_1820_);
lean_dec(v_val_1817_);
lean_dec(v_val_1806_);
lean_dec_ref(v_type_1790_);
v_a_1874_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1834_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1834_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec(v_a_1829_);
lean_dec_ref(v___x_1820_);
lean_dec(v_val_1817_);
lean_dec(v_val_1806_);
lean_dec_ref(v_type_1790_);
v___x_1883_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1, &l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_once, _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1);
v___x_1884_ = l_Lean_indentExpr(v_a_1827_);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1791_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; uint8_t v_verbose_1888_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v_verbose_1888_ = lean_ctor_get_uint8(v_a_1887_, 0);
lean_dec(v_a_1887_);
if (v_verbose_1888_ == 0)
{
lean_dec_ref_known(v___x_1885_, 2);
goto v___jp_1798_;
}
else
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_Meta_Sym_reportIssue(v___x_1885_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_dec_ref_known(v___x_1889_, 1);
goto v___jp_1798_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec_ref_known(v___x_1885_, 2);
v_a_1898_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1886_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1886_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
else
{
lean_dec(v_a_1827_);
lean_dec_ref(v___x_1820_);
lean_dec(v_val_1817_);
lean_dec(v_val_1806_);
lean_dec_ref(v_type_1790_);
return v___x_1828_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec_ref(v___x_1820_);
lean_dec(v_val_1817_);
lean_dec(v_val_1806_);
lean_dec_ref(v_type_1790_);
v_a_1906_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1826_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1826_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v___x_1820_);
lean_dec(v_val_1817_);
lean_dec(v_val_1806_);
lean_dec_ref(v_type_1790_);
v_a_1914_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1824_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1824_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
lean_dec(v_a_1813_);
lean_dec_ref_known(v___x_1809_, 2);
lean_dec(v_val_1806_);
lean_dec_ref(v_type_1790_);
v___x_1922_ = lean_box(0);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1922_);
v___x_1924_ = v___x_1815_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref_known(v___x_1809_, 2);
lean_dec(v_val_1806_);
lean_dec_ref(v_type_1790_);
v_a_1927_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1812_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1812_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
lean_dec(v_a_1802_);
lean_dec_ref(v_type_1790_);
v___x_1935_ = lean_box(0);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1935_);
v___x_1937_ = v___x_1804_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
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
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec_ref(v_type_1790_);
v_a_1940_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1801_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1801_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
v___jp_1798_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(lean_object* v_type_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___lam__0(lean_object* v___x_1957_, lean_object* v_s_1958_){
_start:
{
lean_object* v_exp_1959_; lean_object* v_rings_1960_; lean_object* v_semirings_1961_; lean_object* v_ncRings_1962_; lean_object* v_ncSemirings_1963_; lean_object* v_typeClassify_1964_; lean_object* v_orders_1965_; lean_object* v_typeOrderClassify_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
v_exp_1959_ = lean_ctor_get(v_s_1958_, 0);
v_rings_1960_ = lean_ctor_get(v_s_1958_, 1);
v_semirings_1961_ = lean_ctor_get(v_s_1958_, 2);
v_ncRings_1962_ = lean_ctor_get(v_s_1958_, 3);
v_ncSemirings_1963_ = lean_ctor_get(v_s_1958_, 4);
v_typeClassify_1964_ = lean_ctor_get(v_s_1958_, 5);
v_orders_1965_ = lean_ctor_get(v_s_1958_, 6);
v_typeOrderClassify_1966_ = lean_ctor_get(v_s_1958_, 7);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_s_1958_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1968_ = v_s_1958_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_typeOrderClassify_1966_);
lean_inc(v_orders_1965_);
lean_inc(v_typeClassify_1964_);
lean_inc(v_ncSemirings_1963_);
lean_inc(v_ncRings_1962_);
lean_inc(v_semirings_1961_);
lean_inc(v_rings_1960_);
lean_inc(v_exp_1959_);
lean_dec(v_s_1958_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_array_push(v_ncSemirings_1963_, v___x_1957_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_exp_1959_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_rings_1960_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_semirings_1961_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_ncRings_1962_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1973_, 5, v_typeClassify_1964_);
lean_ctor_set(v_reuseFailAlloc_1973_, 6, v_orders_1965_);
lean_ctor_set(v_reuseFailAlloc_1973_, 7, v_typeOrderClassify_1966_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(lean_object* v_type_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___x_1983_; 
lean_inc_ref(v_type_1975_);
v___x_1983_ = l_Lean_Meta_getDecLevel_x3f(v_type_1975_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2069_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_2069_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2069_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
if (lean_obj_tag(v_a_1984_) == 1)
{
lean_object* v_val_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_del_object(v___x_1986_);
v_val_1988_ = lean_ctor_get(v_a_1984_, 0);
lean_inc_n(v_val_1988_, 2);
lean_dec_ref_known(v_a_1984_, 1);
v___x_1989_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRingQ_x3f___closed__16));
v___x_1990_ = lean_box(0);
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v_val_1988_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = l_Lean_mkConst(v___x_1989_, v___x_1991_);
lean_inc_ref(v_type_1975_);
v___x_1993_ = l_Lean_Expr_app___override(v___x_1992_, v_type_1975_);
v___x_1994_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1993_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2056_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2056_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2056_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
if (lean_obj_tag(v_a_1995_) == 1)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2051_; 
lean_del_object(v___x_1997_);
v_val_1999_ = lean_ctor_get(v_a_1995_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_a_1995_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2001_ = v_a_1995_;
v_isShared_2002_ = v_isSharedCheck_2051_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_val_1999_);
lean_dec(v_a_1995_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2051_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; 
lean_inc(v_val_1999_);
lean_inc_ref(v_type_1975_);
lean_inc(v_val_1988_);
v___x_2003_ = l_Lean_Meta_Sym_Arith_getCharInfo(v_val_1988_, v_type_1975_, v_val_1999_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1977_, v_a_1980_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v_ncSemirings_2007_; lean_object* v_inst_x3f_2008_; uint8_t v_symbolic_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___f_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2005_, 1);
v_ncSemirings_2007_ = lean_ctor_get(v_a_2006_, 4);
lean_inc_ref(v_ncSemirings_2007_);
lean_dec(v_a_2006_);
v_inst_x3f_2008_ = lean_ctor_get(v_a_2004_, 0);
lean_inc(v_inst_x3f_2008_);
v_symbolic_2009_ = lean_ctor_get_uint8(v_a_2004_, sizeof(void*)*1);
lean_dec(v_a_2004_);
v___x_2010_ = lean_array_get_size(v_ncSemirings_2007_);
lean_dec_ref(v_ncSemirings_2007_);
v___x_2011_ = lean_box(0);
v___x_2012_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2012_, 0, v___x_2010_);
lean_ctor_set(v___x_2012_, 1, v_type_1975_);
lean_ctor_set(v___x_2012_, 2, v_val_1988_);
lean_ctor_set(v___x_2012_, 3, v_val_1999_);
lean_ctor_set(v___x_2012_, 4, v_inst_x3f_2008_);
lean_ctor_set(v___x_2012_, 5, v___x_2011_);
lean_ctor_set(v___x_2012_, 6, v___x_2011_);
lean_ctor_set(v___x_2012_, 7, v___x_2011_);
lean_ctor_set(v___x_2012_, 8, v___x_2011_);
lean_ctor_set(v___x_2012_, 9, v___x_2011_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*10, v_symbolic_2009_);
v___f_2013_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2013_, 0, v___x_2012_);
v___x_2014_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2015_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2014_, v___f_2013_, v_a_1977_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2025_; 
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_2015_, 0);
lean_dec(v_unused_2026_);
v___x_2017_ = v___x_2015_;
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
else
{
lean_dec(v___x_2015_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2025_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2010_);
v___x_2020_ = v___x_2001_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2010_);
v___x_2020_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2022_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2020_);
v___x_2022_ = v___x_2017_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_del_object(v___x_2001_);
v_a_2027_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2015_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2015_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v_a_2004_);
lean_del_object(v___x_2001_);
lean_dec(v_val_1999_);
lean_dec(v_val_1988_);
lean_dec_ref(v_type_1975_);
v_a_2035_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2005_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2005_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_del_object(v___x_2001_);
lean_dec(v_val_1999_);
lean_dec(v_val_1988_);
lean_dec_ref(v_type_1975_);
v_a_2043_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2003_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2003_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
lean_dec(v_a_1995_);
lean_dec(v_val_1988_);
lean_dec_ref(v_type_1975_);
v___x_2052_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2052_);
v___x_2054_ = v___x_1997_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_val_1988_);
lean_dec_ref(v_type_1975_);
v_a_2057_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_1994_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_1994_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
lean_dec(v_a_1984_);
lean_dec_ref(v_type_1975_);
v___x_2065_ = lean_box(0);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_2065_);
v___x_2067_ = v___x_1986_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v_type_1975_);
v_a_2070_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_1983_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_1983_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(lean_object* v_type_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(v_type_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(lean_object* v_type_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v___x_2095_; 
lean_inc_ref(v_type_2087_);
v___x_2095_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2190_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2190_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2190_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
if (lean_obj_tag(v_a_2096_) == 1)
{
lean_object* v_val_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v_type_2087_);
v_val_2100_ = lean_ctor_get(v_a_2096_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2096_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2102_ = v_a_2096_;
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_val_2100_);
lean_dec(v_a_2096_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2110_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set_tag(v___x_2102_, 0);
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_val_2100_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2105_);
v___x_2107_ = v___x_2098_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v___x_2111_; 
lean_del_object(v___x_2098_);
lean_dec(v_a_2096_);
lean_inc_ref(v_type_2087_);
v___x_2111_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2181_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2181_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2181_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
if (lean_obj_tag(v_a_2112_) == 1)
{
lean_object* v_val_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2126_; 
lean_dec_ref(v_type_2087_);
v_val_2116_ = lean_ctor_get(v_a_2112_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_a_2112_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2118_ = v_a_2112_;
v_isShared_2119_ = v_isSharedCheck_2126_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_val_2116_);
lean_dec(v_a_2112_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2126_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_val_2116_);
v___x_2121_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2123_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2121_);
v___x_2123_ = v___x_2114_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v___x_2127_; 
lean_del_object(v___x_2114_);
lean_dec(v_a_2112_);
lean_inc_ref(v_type_2087_);
v___x_2127_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2172_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2172_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2172_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
if (lean_obj_tag(v_a_2128_) == 1)
{
lean_object* v_val_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v_type_2087_);
v_val_2132_ = lean_ctor_get(v_a_2128_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_a_2128_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2134_ = v_a_2128_;
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_val_2132_);
lean_dec(v_a_2128_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2142_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
lean_ctor_set_tag(v___x_2134_, 2);
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_val_2132_);
v___x_2137_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2139_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2137_);
v___x_2139_ = v___x_2130_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
lean_object* v___x_2143_; 
lean_del_object(v___x_2130_);
lean_dec(v_a_2128_);
v___x_2143_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(v_type_2087_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2163_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2163_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2163_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
if (lean_obj_tag(v_a_2144_) == 1)
{
lean_object* v_val_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2158_; 
v_val_2148_ = lean_ctor_get(v_a_2144_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_a_2144_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2150_ = v_a_2144_;
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_val_2148_);
lean_dec(v_a_2144_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2158_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
lean_ctor_set_tag(v___x_2150_, 3);
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_val_2148_);
v___x_2153_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2153_);
v___x_2155_ = v___x_2146_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_a_2144_);
v___x_2159_ = lean_box(4);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2159_);
v___x_2161_ = v___x_2146_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
v_a_2164_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2143_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2143_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v_type_2087_);
v_a_2173_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2127_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2127_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec_ref(v_type_2087_);
v_a_2182_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2111_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2111_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v_type_2087_);
v_a_2191_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2095_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2095_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(lean_object* v_type_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(lean_object* v_type_2208_, lean_object* v_a_2209_, lean_object* v_s_2210_){
_start:
{
lean_object* v_exp_2211_; lean_object* v_rings_2212_; lean_object* v_semirings_2213_; lean_object* v_ncRings_2214_; lean_object* v_ncSemirings_2215_; lean_object* v_typeClassify_2216_; lean_object* v_orders_2217_; lean_object* v_typeOrderClassify_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2226_; 
v_exp_2211_ = lean_ctor_get(v_s_2210_, 0);
v_rings_2212_ = lean_ctor_get(v_s_2210_, 1);
v_semirings_2213_ = lean_ctor_get(v_s_2210_, 2);
v_ncRings_2214_ = lean_ctor_get(v_s_2210_, 3);
v_ncSemirings_2215_ = lean_ctor_get(v_s_2210_, 4);
v_typeClassify_2216_ = lean_ctor_get(v_s_2210_, 5);
v_orders_2217_ = lean_ctor_get(v_s_2210_, 6);
v_typeOrderClassify_2218_ = lean_ctor_get(v_s_2210_, 7);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_s_2210_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2220_ = v_s_2210_;
v_isShared_2221_ = v_isSharedCheck_2226_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_typeOrderClassify_2218_);
lean_inc(v_orders_2217_);
lean_inc(v_typeClassify_2216_);
lean_inc(v_ncSemirings_2215_);
lean_inc(v_ncRings_2214_);
lean_inc(v_semirings_2213_);
lean_inc(v_rings_2212_);
lean_inc(v_exp_2211_);
lean_dec(v_s_2210_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2226_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2222_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_2216_, v_type_2208_, v_a_2209_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 5, v___x_2222_);
v___x_2224_ = v___x_2220_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_exp_2211_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_rings_2212_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_semirings_2213_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_ncRings_2214_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v_ncSemirings_2215_);
lean_ctor_set(v_reuseFailAlloc_2225_, 5, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2225_, 6, v_orders_2217_);
lean_ctor_set(v_reuseFailAlloc_2225_, 7, v_typeOrderClassify_2218_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f(lean_object* v_type_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2229_, v_a_2232_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2267_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2267_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2267_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v_typeClassify_2240_; lean_object* v___x_2241_; 
v_typeClassify_2240_ = lean_ctor_get(v_a_2236_, 5);
lean_inc_ref(v_typeClassify_2240_);
lean_dec(v_a_2236_);
v___x_2241_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_2240_, v_type_2227_);
lean_dec_ref(v_typeClassify_2240_);
if (lean_obj_tag(v___x_2241_) == 1)
{
lean_object* v_val_2242_; lean_object* v___x_2244_; 
lean_dec_ref(v_type_2227_);
v_val_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v___x_2241_, 1);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v_val_2242_);
v___x_2244_ = v___x_2238_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_val_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
else
{
lean_object* v___x_2246_; 
lean_dec(v___x_2241_);
lean_del_object(v___x_2238_);
lean_inc_ref(v_type_2227_);
v___x_2246_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___f_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc_n(v_a_2247_, 2);
lean_dec_ref_known(v___x_2246_, 1);
v___f_2248_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_classify_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2248_, 0, v_type_2227_);
lean_closure_set(v___f_2248_, 1, v_a_2247_);
v___x_2249_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2250_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2249_, v___f_2248_, v_a_2229_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; 
v_unused_2258_ = lean_ctor_get(v___x_2250_, 0);
lean_dec(v_unused_2258_);
v___x_2252_ = v___x_2250_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_dec(v___x_2250_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v_a_2247_);
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2247_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_a_2247_);
v_a_2259_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2250_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2250_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_dec_ref(v_type_2227_);
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v_type_2227_);
v_a_2268_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2235_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2235_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classify_x3f___boxed(lean_object* v_type_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_Meta_Sym_Arith_classify_x3f(v_type_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(lean_object* v_fn_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Meta_Sym_canon(v_fn_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2295_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v___x_2295_ = l_Lean_Meta_Sym_shareCommon(v_a_2294_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
return v___x_2295_;
}
else
{
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn___boxed(lean_object* v_fn_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v_fn_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(lean_object* v_u_2310_, lean_object* v_type_2311_, lean_object* v_semiringInst_2312_, lean_object* v_leInst_2313_, lean_object* v_ltInst_2314_, lean_object* v_isPreorderInst_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___closed__1));
v___x_2323_ = lean_box(0);
v___x_2324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2324_, 0, v_u_2310_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = l_Lean_mkConst(v___x_2322_, v___x_2324_);
v___x_2326_ = l_Lean_mkApp5(v___x_2325_, v_type_2311_, v_semiringInst_2312_, v_leInst_2313_, v_ltInst_2314_, v_isPreorderInst_2315_);
v___x_2327_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2326_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg___boxed(lean_object* v_u_2328_, lean_object* v_type_2329_, lean_object* v_semiringInst_2330_, lean_object* v_leInst_2331_, lean_object* v_ltInst_2332_, lean_object* v_isPreorderInst_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_u_2328_, v_type_2329_, v_semiringInst_2330_, v_leInst_2331_, v_ltInst_2332_, v_isPreorderInst_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(lean_object* v_u_2341_, lean_object* v_type_2342_, lean_object* v_semiringInst_2343_, lean_object* v_leInst_2344_, lean_object* v_ltInst_2345_, lean_object* v_isPreorderInst_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_u_2341_, v_type_2342_, v_semiringInst_2343_, v_leInst_2344_, v_ltInst_2345_, v_isPreorderInst_2346_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___boxed(lean_object* v_u_2355_, lean_object* v_type_2356_, lean_object* v_semiringInst_2357_, lean_object* v_leInst_2358_, lean_object* v_ltInst_2359_, lean_object* v_isPreorderInst_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f(v_u_2355_, v_type_2356_, v_semiringInst_2357_, v_leInst_2358_, v_ltInst_2359_, v_isPreorderInst_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f_spec__0(lean_object* v_msg_2369_){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = l_Lean_instInhabitedExpr;
v___x_2371_ = lean_panic_fn_borrowed(v___x_2370_, v_msg_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0(lean_object* v___x_2372_, lean_object* v_s_2373_){
_start:
{
lean_object* v_exp_2374_; lean_object* v_rings_2375_; lean_object* v_semirings_2376_; lean_object* v_ncRings_2377_; lean_object* v_ncSemirings_2378_; lean_object* v_typeClassify_2379_; lean_object* v_orders_2380_; lean_object* v_typeOrderClassify_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2389_; 
v_exp_2374_ = lean_ctor_get(v_s_2373_, 0);
v_rings_2375_ = lean_ctor_get(v_s_2373_, 1);
v_semirings_2376_ = lean_ctor_get(v_s_2373_, 2);
v_ncRings_2377_ = lean_ctor_get(v_s_2373_, 3);
v_ncSemirings_2378_ = lean_ctor_get(v_s_2373_, 4);
v_typeClassify_2379_ = lean_ctor_get(v_s_2373_, 5);
v_orders_2380_ = lean_ctor_get(v_s_2373_, 6);
v_typeOrderClassify_2381_ = lean_ctor_get(v_s_2373_, 7);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_s_2373_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2383_ = v_s_2373_;
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_typeOrderClassify_2381_);
lean_inc(v_orders_2380_);
lean_inc(v_typeClassify_2379_);
lean_inc(v_ncSemirings_2378_);
lean_inc(v_ncRings_2377_);
lean_inc(v_semirings_2376_);
lean_inc(v_rings_2375_);
lean_inc(v_exp_2374_);
lean_dec(v_s_2373_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2389_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2385_ = lean_array_push(v_orders_2380_, v___x_2372_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 6, v___x_2385_);
v___x_2387_ = v___x_2383_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_exp_2374_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_rings_2375_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_semirings_2376_);
lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_ncRings_2377_);
lean_ctor_set(v_reuseFailAlloc_2388_, 4, v_ncSemirings_2378_);
lean_ctor_set(v_reuseFailAlloc_2388_, 5, v_typeClassify_2379_);
lean_ctor_set(v_reuseFailAlloc_2388_, 6, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2388_, 7, v_typeOrderClassify_2381_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(lean_object* v_type_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2412_ = l_Lean_Meta_Sym_Arith_instInhabitedCommRing_default;
v___x_2413_ = l_Lean_Meta_Sym_Arith_instInhabitedRing_default;
v___x_2414_ = l_Lean_Meta_Sym_Arith_instInhabitedCommSemiring_default;
v___x_2415_ = l_Lean_Meta_Sym_Arith_instInhabitedSemiring_default;
lean_inc_ref(v_type_2404_);
v___x_2416_ = l_Lean_Meta_getDecLevel_x3f(v_type_2404_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2756_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2419_ = v___x_2416_;
v_isShared_2420_ = v_isSharedCheck_2756_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2416_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2756_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
if (lean_obj_tag(v_a_2417_) == 1)
{
lean_object* v_val_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2751_; 
lean_del_object(v___x_2419_);
v_val_2421_ = lean_ctor_get(v_a_2417_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_a_2417_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2423_ = v_a_2417_;
v_isShared_2424_ = v_isSharedCheck_2751_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_val_2421_);
lean_dec(v_a_2417_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2751_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__1));
v___x_2426_ = lean_box(0);
lean_inc(v_val_2421_);
v___x_2427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2427_, 0, v_val_2421_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
lean_inc_ref(v___x_2427_);
v___x_2428_ = l_Lean_mkConst(v___x_2425_, v___x_2427_);
lean_inc_ref(v_type_2404_);
v___x_2429_ = l_Lean_Expr_app___override(v___x_2428_, v_type_2404_);
v___x_2430_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2429_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2742_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2742_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2742_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
if (lean_obj_tag(v_a_2431_) == 1)
{
lean_object* v_val_2435_; lean_object* v___x_2436_; 
lean_del_object(v___x_2433_);
v_val_2435_ = lean_ctor_get(v_a_2431_, 0);
lean_inc(v_val_2435_);
lean_inc_ref(v_a_2431_);
lean_inc_ref(v_type_2404_);
lean_inc(v_val_2421_);
v___x_2436_ = l_Lean_Meta_Sym_Arith_mkIsPreorderInst_x3f(v_val_2421_, v_type_2404_, v_a_2431_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2729_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2729_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2729_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
if (lean_obj_tag(v_a_2437_) == 1)
{
lean_object* v_val_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2724_; 
lean_del_object(v___x_2439_);
v_val_2441_ = lean_ctor_get(v_a_2437_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v_a_2437_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2443_ = v_a_2437_;
v_isShared_2444_ = v_isSharedCheck_2724_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_val_2441_);
lean_dec(v_a_2437_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2724_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; 
lean_inc_ref(v_a_2431_);
lean_inc_ref(v_type_2404_);
lean_inc(v_val_2421_);
v___x_2445_ = l_Lean_Meta_Sym_Arith_mkIsPartialOrderInst_x3f(v_val_2421_, v_type_2404_, v_a_2431_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2447_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
lean_inc_ref(v_a_2431_);
lean_inc_ref(v_type_2404_);
lean_inc(v_val_2421_);
v___x_2447_ = l_Lean_Meta_Sym_Arith_mkIsLinearPreorderInst_x3f(v_val_2421_, v_type_2404_, v_a_2431_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2447_, 1);
v___x_2449_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__3));
lean_inc_ref(v___x_2427_);
v___x_2450_ = l_Lean_mkConst(v___x_2449_, v___x_2427_);
lean_inc_ref(v_type_2404_);
v___x_2451_ = l_Lean_Expr_app___override(v___x_2450_, v_type_2404_);
v___x_2452_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_2451_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v___x_2454_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__5));
lean_inc_ref(v___x_2427_);
v___x_2455_ = l_Lean_mkConst(v___x_2454_, v___x_2427_);
lean_inc(v_val_2435_);
lean_inc_ref(v_type_2404_);
v___x_2456_ = l_Lean_mkAppB(v___x_2455_, v_type_2404_, v_val_2435_);
v___x_2457_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v___x_2456_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v_fst_2462_; lean_object* v_fst_2463_; uint8_t v_fst_2464_; lean_object* v_fst_2465_; lean_object* v_fst_2466_; uint8_t v_snd_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v_fst_2506_; lean_object* v_snd_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
if (lean_obj_tag(v_a_2453_) == 1)
{
lean_object* v_val_2513_; lean_object* v___x_2514_; 
v_val_2513_ = lean_ctor_get(v_a_2453_, 0);
lean_inc_ref(v_a_2453_);
lean_inc_ref(v_type_2404_);
lean_inc(v_val_2421_);
v___x_2514_ = l_Lean_Meta_Sym_Arith_mkLawfulOrderLTInst_x3f(v_val_2421_, v_type_2404_, v_a_2453_, v_a_2431_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
if (lean_obj_tag(v_a_2515_) == 0)
{
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
v_fst_2506_ = v_a_2515_;
v_snd_2507_ = v_a_2515_;
v___y_2508_ = v_a_2406_;
v___y_2509_ = v_a_2409_;
goto v___jp_2505_;
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2516_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___closed__7));
v___x_2517_ = l_Lean_mkConst(v___x_2516_, v___x_2427_);
lean_inc(v_val_2513_);
lean_inc_ref(v_type_2404_);
v___x_2518_ = l_Lean_mkAppB(v___x_2517_, v_type_2404_, v_val_2513_);
v___x_2519_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_canonFn(v___x_2518_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2522_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2519_, 1);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v_a_2520_);
v___x_2522_ = v___x_2423_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2520_);
v___x_2522_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
uint8_t v___x_2523_; uint8_t v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = 0;
v___x_2524_ = 1;
lean_inc_ref(v_type_2404_);
v___x_2525_ = l_Lean_Meta_Sym_Arith_classify_x3f(v_type_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
switch(lean_obj_tag(v_a_2526_))
{
case 0:
{
lean_object* v_id_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2562_; 
v_id_2527_ = lean_ctor_get(v_a_2526_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_a_2526_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2529_ = v_a_2526_;
v_isShared_2530_ = v_isSharedCheck_2562_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_id_2527_);
lean_dec(v_a_2526_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2562_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2406_, v_a_2409_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v_rings_2533_; lean_object* v___x_2534_; lean_object* v_toRing_2535_; lean_object* v_ringInst_2536_; lean_object* v_semiringInst_2537_; lean_object* v___x_2538_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v_rings_2533_ = lean_ctor_get(v_a_2532_, 1);
lean_inc_ref(v_rings_2533_);
lean_dec(v_a_2532_);
v___x_2534_ = lean_array_get(v___x_2412_, v_rings_2533_, v_id_2527_);
lean_dec_ref(v_rings_2533_);
v_toRing_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc_ref(v_toRing_2535_);
lean_dec(v___x_2534_);
v_ringInst_2536_ = lean_ctor_get(v_toRing_2535_, 3);
lean_inc_ref(v_ringInst_2536_);
v_semiringInst_2537_ = lean_ctor_get(v_toRing_2535_, 4);
lean_inc_ref(v_semiringInst_2537_);
lean_dec_ref(v_toRing_2535_);
lean_inc(v_val_2441_);
lean_inc(v_val_2513_);
lean_inc(v_val_2435_);
lean_inc_ref(v_type_2404_);
lean_inc(v_val_2421_);
v___x_2538_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2421_, v_type_2404_, v_semiringInst_2537_, v_val_2435_, v_val_2513_, v_val_2441_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
if (lean_obj_tag(v_a_2539_) == 1)
{
lean_object* v___x_2541_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set_tag(v___x_2529_, 1);
v___x_2541_ = v___x_2529_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_id_2527_);
v___x_2541_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2543_, 0, v_ringInst_2536_);
v___y_2460_ = v___x_2522_;
v___y_2461_ = v_a_2515_;
v_fst_2462_ = v___x_2541_;
v_fst_2463_ = v___x_2542_;
v_fst_2464_ = v___x_2524_;
v_fst_2465_ = v___x_2543_;
v_fst_2466_ = v_a_2539_;
v_snd_2467_ = v___x_2524_;
v___y_2468_ = v_a_2406_;
v___y_2469_ = v_a_2409_;
goto v___jp_2459_;
}
}
else
{
lean_object* v___x_2545_; 
lean_dec(v_a_2539_);
lean_dec_ref(v_ringInst_2536_);
lean_del_object(v___x_2529_);
lean_dec(v_id_2527_);
v___x_2545_ = lean_box(0);
v___y_2460_ = v___x_2522_;
v___y_2461_ = v_a_2515_;
v_fst_2462_ = v___x_2545_;
v_fst_2463_ = v___x_2545_;
v_fst_2464_ = v___x_2524_;
v_fst_2465_ = v___x_2545_;
v_fst_2466_ = v___x_2545_;
v_snd_2467_ = v___x_2524_;
v___y_2468_ = v_a_2406_;
v___y_2469_ = v_a_2409_;
goto v___jp_2459_;
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v_ringInst_2536_);
lean_del_object(v___x_2529_);
lean_dec(v_id_2527_);
lean_dec_ref(v___x_2522_);
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2546_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2538_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2538_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_del_object(v___x_2529_);
lean_dec(v_id_2527_);
lean_dec_ref(v___x_2522_);
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2554_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2531_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2531_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
case 1:
{
lean_object* v_id_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2597_; 
v_id_2563_ = lean_ctor_get(v_a_2526_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_a_2526_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2565_ = v_a_2526_;
v_isShared_2566_ = v_isSharedCheck_2597_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_id_2563_);
lean_dec(v_a_2526_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2597_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2406_, v_a_2409_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v_ncRings_2569_; lean_object* v___x_2570_; lean_object* v_ringInst_2571_; lean_object* v_semiringInst_2572_; lean_object* v___x_2573_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
v_ncRings_2569_ = lean_ctor_get(v_a_2568_, 3);
lean_inc_ref(v_ncRings_2569_);
lean_dec(v_a_2568_);
v___x_2570_ = lean_array_get(v___x_2413_, v_ncRings_2569_, v_id_2563_);
lean_dec_ref(v_ncRings_2569_);
v_ringInst_2571_ = lean_ctor_get(v___x_2570_, 3);
lean_inc_ref(v_ringInst_2571_);
v_semiringInst_2572_ = lean_ctor_get(v___x_2570_, 4);
lean_inc_ref(v_semiringInst_2572_);
lean_dec(v___x_2570_);
lean_inc(v_val_2441_);
lean_inc(v_val_2513_);
lean_inc(v_val_2435_);
lean_inc_ref(v_type_2404_);
lean_inc(v_val_2421_);
v___x_2573_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2421_, v_type_2404_, v_semiringInst_2572_, v_val_2435_, v_val_2513_, v_val_2441_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
if (lean_obj_tag(v_a_2574_) == 1)
{
lean_object* v___x_2576_; 
if (v_isShared_2566_ == 0)
{
v___x_2576_ = v___x_2565_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_id_2563_);
v___x_2576_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = lean_box(0);
v___x_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2578_, 0, v_ringInst_2571_);
v___y_2460_ = v___x_2522_;
v___y_2461_ = v_a_2515_;
v_fst_2462_ = v___x_2576_;
v_fst_2463_ = v___x_2577_;
v_fst_2464_ = v___x_2524_;
v_fst_2465_ = v___x_2578_;
v_fst_2466_ = v_a_2574_;
v_snd_2467_ = v___x_2523_;
v___y_2468_ = v_a_2406_;
v___y_2469_ = v_a_2409_;
goto v___jp_2459_;
}
}
else
{
lean_object* v___x_2580_; 
lean_dec(v_a_2574_);
lean_dec_ref(v_ringInst_2571_);
lean_del_object(v___x_2565_);
lean_dec(v_id_2563_);
v___x_2580_ = lean_box(0);
v___y_2460_ = v___x_2522_;
v___y_2461_ = v_a_2515_;
v_fst_2462_ = v___x_2580_;
v_fst_2463_ = v___x_2580_;
v_fst_2464_ = v___x_2524_;
v_fst_2465_ = v___x_2580_;
v_fst_2466_ = v___x_2580_;
v_snd_2467_ = v___x_2523_;
v___y_2468_ = v_a_2406_;
v___y_2469_ = v_a_2409_;
goto v___jp_2459_;
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec_ref(v_ringInst_2571_);
lean_del_object(v___x_2565_);
lean_dec(v_id_2563_);
lean_dec_ref(v___x_2522_);
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2581_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2573_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2573_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2596_; 
lean_del_object(v___x_2565_);
lean_dec(v_id_2563_);
lean_dec_ref(v___x_2522_);
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2589_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2596_ == 0)
{
v___x_2591_ = v___x_2567_;
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2567_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2596_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2594_; 
if (v_isShared_2592_ == 0)
{
v___x_2594_ = v___x_2591_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
case 2:
{
lean_object* v_id_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2631_; 
v_id_2598_ = lean_ctor_get(v_a_2526_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_a_2526_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2600_ = v_a_2526_;
v_isShared_2601_ = v_isSharedCheck_2631_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_id_2598_);
lean_dec(v_a_2526_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2631_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2406_, v_a_2409_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v_semirings_2604_; lean_object* v___x_2605_; lean_object* v_toSemiring_2606_; lean_object* v_semiringInst_2607_; lean_object* v___x_2608_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_a_2603_);
lean_dec_ref_known(v___x_2602_, 1);
v_semirings_2604_ = lean_ctor_get(v_a_2603_, 2);
lean_inc_ref(v_semirings_2604_);
lean_dec(v_a_2603_);
v___x_2605_ = lean_array_get(v___x_2414_, v_semirings_2604_, v_id_2598_);
lean_dec_ref(v_semirings_2604_);
v_toSemiring_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc_ref(v_toSemiring_2606_);
lean_dec(v___x_2605_);
v_semiringInst_2607_ = lean_ctor_get(v_toSemiring_2606_, 3);
lean_inc_ref(v_semiringInst_2607_);
lean_dec_ref(v_toSemiring_2606_);
lean_inc(v_val_2441_);
lean_inc(v_val_2513_);
lean_inc(v_val_2435_);
lean_inc_ref(v_type_2404_);
lean_inc(v_val_2421_);
v___x_2608_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2421_, v_type_2404_, v_semiringInst_2607_, v_val_2435_, v_val_2513_, v_val_2441_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
if (lean_obj_tag(v_a_2609_) == 1)
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2610_ = lean_box(0);
if (v_isShared_2601_ == 0)
{
lean_ctor_set_tag(v___x_2600_, 1);
v___x_2612_ = v___x_2600_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_id_2598_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
v___y_2460_ = v___x_2522_;
v___y_2461_ = v_a_2515_;
v_fst_2462_ = v___x_2610_;
v_fst_2463_ = v___x_2612_;
v_fst_2464_ = v___x_2524_;
v_fst_2465_ = v___x_2610_;
v_fst_2466_ = v_a_2609_;
v_snd_2467_ = v___x_2523_;
v___y_2468_ = v_a_2406_;
v___y_2469_ = v_a_2409_;
goto v___jp_2459_;
}
}
else
{
lean_object* v___x_2614_; 
lean_dec(v_a_2609_);
lean_del_object(v___x_2600_);
lean_dec(v_id_2598_);
v___x_2614_ = lean_box(0);
v___y_2460_ = v___x_2522_;
v___y_2461_ = v_a_2515_;
v_fst_2462_ = v___x_2614_;
v_fst_2463_ = v___x_2614_;
v_fst_2464_ = v___x_2524_;
v_fst_2465_ = v___x_2614_;
v_fst_2466_ = v___x_2614_;
v_snd_2467_ = v___x_2523_;
v___y_2468_ = v_a_2406_;
v___y_2469_ = v_a_2409_;
goto v___jp_2459_;
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_del_object(v___x_2600_);
lean_dec(v_id_2598_);
lean_dec_ref(v___x_2522_);
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2615_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2608_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2608_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_del_object(v___x_2600_);
lean_dec(v_id_2598_);
lean_dec_ref(v___x_2522_);
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2623_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2602_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2602_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
case 3:
{
lean_object* v_id_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2664_; 
v_id_2632_ = lean_ctor_get(v_a_2526_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_a_2526_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2634_ = v_a_2526_;
v_isShared_2635_ = v_isSharedCheck_2664_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_id_2632_);
lean_dec(v_a_2526_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2664_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2406_, v_a_2409_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v_ncSemirings_2638_; lean_object* v___x_2639_; lean_object* v_semiringInst_2640_; lean_object* v___x_2641_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v_ncSemirings_2638_ = lean_ctor_get(v_a_2637_, 4);
lean_inc_ref(v_ncSemirings_2638_);
lean_dec(v_a_2637_);
v___x_2639_ = lean_array_get(v___x_2415_, v_ncSemirings_2638_, v_id_2632_);
lean_dec_ref(v_ncSemirings_2638_);
v_semiringInst_2640_ = lean_ctor_get(v___x_2639_, 3);
lean_inc_ref(v_semiringInst_2640_);
lean_dec(v___x_2639_);
lean_inc(v_val_2441_);
lean_inc(v_val_2513_);
lean_inc(v_val_2435_);
lean_inc_ref(v_type_2404_);
lean_inc(v_val_2421_);
v___x_2641_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_mkOrderedRingInst_x3f___redArg(v_val_2421_, v_type_2404_, v_semiringInst_2640_, v_val_2435_, v_val_2513_, v_val_2441_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
if (lean_obj_tag(v_a_2642_) == 1)
{
lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2643_ = lean_box(0);
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 1);
v___x_2645_ = v___x_2634_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_id_2632_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
v___y_2460_ = v___x_2522_;
v___y_2461_ = v_a_2515_;
v_fst_2462_ = v___x_2643_;
v_fst_2463_ = v___x_2645_;
v_fst_2464_ = v___x_2523_;
v_fst_2465_ = v___x_2643_;
v_fst_2466_ = v_a_2642_;
v_snd_2467_ = v___x_2523_;
v___y_2468_ = v_a_2406_;
v___y_2469_ = v_a_2409_;
goto v___jp_2459_;
}
}
else
{
lean_object* v___x_2647_; 
lean_dec(v_a_2642_);
lean_del_object(v___x_2634_);
lean_dec(v_id_2632_);
v___x_2647_ = lean_box(0);
v___y_2460_ = v___x_2522_;
v___y_2461_ = v_a_2515_;
v_fst_2462_ = v___x_2647_;
v_fst_2463_ = v___x_2647_;
v_fst_2464_ = v___x_2524_;
v_fst_2465_ = v___x_2647_;
v_fst_2466_ = v___x_2647_;
v_snd_2467_ = v___x_2523_;
v___y_2468_ = v_a_2406_;
v___y_2469_ = v_a_2409_;
goto v___jp_2459_;
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_del_object(v___x_2634_);
lean_dec(v_id_2632_);
lean_dec_ref(v___x_2522_);
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2648_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2641_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2641_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_del_object(v___x_2634_);
lean_dec(v_id_2632_);
lean_dec_ref(v___x_2522_);
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2656_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2636_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2636_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
default: 
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_box(0);
v___y_2460_ = v___x_2522_;
v___y_2461_ = v_a_2515_;
v_fst_2462_ = v___x_2665_;
v_fst_2463_ = v___x_2665_;
v_fst_2464_ = v___x_2524_;
v_fst_2465_ = v___x_2665_;
v_fst_2466_ = v___x_2665_;
v_snd_2467_ = v___x_2523_;
v___y_2468_ = v_a_2406_;
v___y_2469_ = v_a_2409_;
goto v___jp_2459_;
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v___x_2522_);
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2666_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2525_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2525_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec_ref_known(v_a_2515_, 1);
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2675_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2519_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2519_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec_ref_known(v_a_2453_, 1);
lean_dec(v_a_2458_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2683_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2514_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2514_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_object* v___x_2691_; 
lean_dec_ref_known(v_a_2431_, 1);
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
v___x_2691_ = lean_box(0);
v_fst_2506_ = v___x_2691_;
v_snd_2507_ = v___x_2691_;
v___y_2508_ = v_a_2406_;
v___y_2509_ = v_a_2409_;
goto v___jp_2505_;
}
v___jp_2459_:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v___y_2468_, v___y_2469_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v_orders_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v_orders_2472_ = lean_ctor_get(v_a_2471_, 6);
lean_inc_ref(v_orders_2472_);
lean_dec(v_a_2471_);
v___x_2473_ = lean_array_get_size(v_orders_2472_);
lean_dec_ref(v_orders_2472_);
v___x_2474_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
lean_ctor_set(v___x_2474_, 1, v_type_2404_);
lean_ctor_set(v___x_2474_, 2, v_val_2421_);
lean_ctor_set(v___x_2474_, 3, v_val_2441_);
lean_ctor_set(v___x_2474_, 4, v_val_2435_);
lean_ctor_set(v___x_2474_, 5, v_a_2453_);
lean_ctor_set(v___x_2474_, 6, v_a_2446_);
lean_ctor_set(v___x_2474_, 7, v_a_2448_);
lean_ctor_set(v___x_2474_, 8, v___y_2461_);
lean_ctor_set(v___x_2474_, 9, v_fst_2462_);
lean_ctor_set(v___x_2474_, 10, v_fst_2463_);
lean_ctor_set(v___x_2474_, 11, v_fst_2465_);
lean_ctor_set(v___x_2474_, 12, v_fst_2466_);
lean_ctor_set(v___x_2474_, 13, v_a_2458_);
lean_ctor_set(v___x_2474_, 14, v___y_2460_);
lean_ctor_set_uint8(v___x_2474_, sizeof(void*)*15, v_snd_2467_);
lean_ctor_set_uint8(v___x_2474_, sizeof(void*)*15 + 1, v_fst_2464_);
v___f_2475_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___lam__0), 2, 1);
lean_closure_set(v___f_2475_, 0, v___x_2474_);
v___x_2476_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2477_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2476_, v___f_2475_, v___y_2468_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2487_; 
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; 
v_unused_2488_ = lean_ctor_get(v___x_2477_, 0);
lean_dec(v_unused_2488_);
v___x_2479_ = v___x_2477_;
v_isShared_2480_ = v_isSharedCheck_2487_;
goto v_resetjp_2478_;
}
else
{
lean_dec(v___x_2477_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2487_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2473_);
v___x_2482_ = v___x_2443_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2473_);
v___x_2482_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2484_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v___x_2482_);
v___x_2484_ = v___x_2479_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_del_object(v___x_2443_);
v_a_2489_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2477_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2477_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_fst_2466_);
lean_dec(v_fst_2465_);
lean_dec(v_fst_2463_);
lean_dec(v_fst_2462_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec(v_a_2458_);
lean_dec(v_a_2453_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2497_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2470_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2470_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
v___jp_2505_:
{
uint8_t v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2510_ = 1;
v___x_2511_ = lean_box(0);
v___x_2512_ = 0;
lean_inc_n(v_fst_2506_, 2);
v___y_2460_ = v_snd_2507_;
v___y_2461_ = v_fst_2506_;
v_fst_2462_ = v___x_2511_;
v_fst_2463_ = v___x_2511_;
v_fst_2464_ = v___x_2510_;
v_fst_2465_ = v_fst_2506_;
v_fst_2466_ = v_fst_2506_;
v_snd_2467_ = v___x_2512_;
v___y_2468_ = v___y_2508_;
v___y_2469_ = v___y_2509_;
goto v___jp_2459_;
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_a_2453_);
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec_ref_known(v_a_2431_, 1);
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2692_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2457_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2457_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_a_2448_);
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec_ref_known(v_a_2431_, 1);
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2700_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2452_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2452_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec(v_a_2446_);
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec(v_val_2435_);
lean_dec_ref_known(v_a_2431_, 1);
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2708_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2447_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2447_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_del_object(v___x_2443_);
lean_dec(v_val_2441_);
lean_dec_ref_known(v_a_2431_, 1);
lean_dec(v_val_2435_);
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2716_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2445_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2445_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
}
else
{
lean_object* v___x_2725_; lean_object* v___x_2727_; 
lean_dec(v_a_2437_);
lean_dec(v_val_2435_);
lean_dec_ref_known(v_a_2431_, 1);
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v___x_2725_ = lean_box(0);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2725_);
v___x_2727_ = v___x_2439_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v_val_2435_);
lean_dec_ref_known(v_a_2431_, 1);
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2730_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2436_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2436_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_dec(v_a_2431_);
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v___x_2738_ = lean_box(0);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2738_);
v___x_2740_ = v___x_2433_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref_known(v___x_2427_, 2);
lean_del_object(v___x_2423_);
lean_dec(v_val_2421_);
lean_dec_ref(v_type_2404_);
v_a_2743_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2430_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2430_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
lean_dec(v_a_2417_);
lean_dec_ref(v_type_2404_);
v___x_2752_ = lean_box(0);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2752_);
v___x_2754_ = v___x_2419_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_dec_ref(v_type_2404_);
v_a_2757_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2416_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2416_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f___boxed(lean_object* v_type_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(v_type_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0(lean_object* v_type_2774_, lean_object* v_a_2775_, lean_object* v_s_2776_){
_start:
{
lean_object* v_exp_2777_; lean_object* v_rings_2778_; lean_object* v_semirings_2779_; lean_object* v_ncRings_2780_; lean_object* v_ncSemirings_2781_; lean_object* v_typeClassify_2782_; lean_object* v_orders_2783_; lean_object* v_typeOrderClassify_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2792_; 
v_exp_2777_ = lean_ctor_get(v_s_2776_, 0);
v_rings_2778_ = lean_ctor_get(v_s_2776_, 1);
v_semirings_2779_ = lean_ctor_get(v_s_2776_, 2);
v_ncRings_2780_ = lean_ctor_get(v_s_2776_, 3);
v_ncSemirings_2781_ = lean_ctor_get(v_s_2776_, 4);
v_typeClassify_2782_ = lean_ctor_get(v_s_2776_, 5);
v_orders_2783_ = lean_ctor_get(v_s_2776_, 6);
v_typeOrderClassify_2784_ = lean_ctor_get(v_s_2776_, 7);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_s_2776_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2786_ = v_s_2776_;
v_isShared_2787_ = v_isSharedCheck_2792_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_typeOrderClassify_2784_);
lean_inc(v_orders_2783_);
lean_inc(v_typeClassify_2782_);
lean_inc(v_ncSemirings_2781_);
lean_inc(v_ncRings_2780_);
lean_inc(v_semirings_2779_);
lean_inc(v_rings_2778_);
lean_inc(v_exp_2777_);
lean_dec(v_s_2776_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2792_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2788_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeOrderClassify_2784_, v_type_2774_, v_a_2775_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 7, v___x_2788_);
v___x_2790_ = v___x_2786_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_exp_2777_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_rings_2778_);
lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_semirings_2779_);
lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_ncRings_2780_);
lean_ctor_set(v_reuseFailAlloc_2791_, 4, v_ncSemirings_2781_);
lean_ctor_set(v_reuseFailAlloc_2791_, 5, v_typeClassify_2782_);
lean_ctor_set(v_reuseFailAlloc_2791_, 6, v_orders_2783_);
lean_ctor_set(v_reuseFailAlloc_2791_, 7, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f(lean_object* v_type_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2795_, v_a_2798_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2833_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2833_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2833_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v_typeOrderClassify_2806_; lean_object* v___x_2807_; 
v_typeOrderClassify_2806_ = lean_ctor_get(v_a_2802_, 7);
lean_inc_ref(v_typeOrderClassify_2806_);
lean_dec(v_a_2802_);
v___x_2807_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeOrderClassify_2806_, v_type_2793_);
lean_dec_ref(v_typeOrderClassify_2806_);
if (lean_obj_tag(v___x_2807_) == 1)
{
lean_object* v_val_2808_; lean_object* v___x_2810_; 
lean_dec_ref(v_type_2793_);
v_val_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v___x_2807_, 1);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v_val_2808_);
v___x_2810_ = v___x_2804_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_val_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
else
{
lean_object* v___x_2812_; 
lean_dec(v___x_2807_);
lean_del_object(v___x_2804_);
lean_inc_ref(v_type_2793_);
v___x_2812_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryOrder_x3f(v_type_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___f_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc_n(v_a_2813_, 2);
lean_dec_ref_known(v___x_2812_, 1);
v___f_2814_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_classifyOrder_x3f___lam__0), 3, 2);
lean_closure_set(v___f_2814_, 0, v_type_2793_);
lean_closure_set(v___f_2814_, 1, v_a_2813_);
v___x_2815_ = l_Lean_Meta_Sym_Arith_arithExt;
v___x_2816_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2815_, v___f_2814_, v_a_2795_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2816_, 0);
lean_dec(v_unused_2824_);
v___x_2818_ = v___x_2816_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v___x_2816_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v_a_2813_);
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2813_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_a_2813_);
v_a_2825_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2816_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2816_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
else
{
lean_dec_ref(v_type_2793_);
return v___x_2812_;
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec_ref(v_type_2793_);
v_a_2834_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2801_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2801_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_classifyOrder_x3f___boxed(lean_object* v_type_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Lean_Meta_Sym_Arith_classifyOrder_x3f(v_type_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
return v_res_2850_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Insts(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Canon(uint8_t builtin);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Insts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_Classify(builtin);
}
#ifdef __cplusplus
}
#endif
