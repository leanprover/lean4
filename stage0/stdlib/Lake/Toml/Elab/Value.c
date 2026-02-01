// Lean compiler output
// Module: Lake.Toml.Elab.Value
// Imports: public import Lean.CoreM public import Lake.Toml.Data.Value public import Lake.Toml.Grammar meta import all Lake.Toml.Grammar
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ill-formed "};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
extern lean_object* l_Lean_Core_instMonadRefCoreM;
extern lean_object* l_Lean_Core_instAddMessageContextCoreM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__6;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Toml"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "boolean"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 74, 28, 167, 158, 175, 30, 0)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invalid boolean"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value),LEAN_SCALAR_PTR_LITERAL(94, 186, 129, 3, 94, 77, 39, 82)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value),LEAN_SCALAR_PTR_LITERAL(45, 94, 147, 128, 103, 18, 162, 55)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decInt"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 5, 249, 175, 125, 238, 54, 100)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "ill-formed decimal integer syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0 = (const lean_object*)&l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2;
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inf"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nan"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value;
double lean_float_of_nat(lean_object*);
static double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_negate(double);
double lean_float_div(double, double);
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "float"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 154, 151, 104, 68, 255, 246, 246)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed float syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binNum"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 60, 170, 39, 77, 137, 193, 6)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed binary number syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "octNum"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 70, 221, 168, 145, 119, 144, 197)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed octal number syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexNum"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 174, 95, 211, 123, 63, 171, 252)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "ill-formed hexadecimal number syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "invalid date-time"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dateTime"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value),LEAN_SCALAR_PTR_LITERAL(100, 234, 1, 129, 172, 254, 231, 202)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "ill-formed date-time syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6;
lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "literalString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 168, 165, 209, 230, 255, 154, 83)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed literalString syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4;
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3;
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid unicode escape `"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3;
lean_object* lean_substring_tostring(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "basicString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 34, 208, 112, 75, 114, 213, 233)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed basic string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "mlLiteralString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 215, 18, 247, 52, 33, 2, 54)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "ill-formed multi-line literal string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mlBasicString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 27, 188, 79, 217, 46, 221, 25)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "ill-formed multi-line basic string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "string"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 134, 223, 178, 21, 25, 142, 203)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ill-formed string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unquotedKey"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 43, 232, 206, 44, 188, 39, 241)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed unquoted key syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_elabSimpleKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpleKey"};
static const lean_object* l_Lake_Toml_elabSimpleKey___closed__0 = (const lean_object*)&l_Lake_Toml_elabSimpleKey___closed__0_value;
static const lean_ctor_object l_Lake_Toml_elabSimpleKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_elabSimpleKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabSimpleKey___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_elabSimpleKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabSimpleKey___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_elabSimpleKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 51, 117, 190, 121, 223, 170, 220)}};
static const lean_object* l_Lake_Toml_elabSimpleKey___closed__1 = (const lean_object*)&l_Lake_Toml_elabSimpleKey___closed__1_value;
static const lean_string_object l_Lake_Toml_elabSimpleKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed simple key syntax"};
static const lean_object* l_Lake_Toml_elabSimpleKey___closed__2 = (const lean_object*)&l_Lake_Toml_elabSimpleKey___closed__2_value;
static lean_object* l_Lake_Toml_elabSimpleKey___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "array"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 212, 239, 77, 14, 34, 57, 134)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed array syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_quickCmp___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cannot redefine key `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lake_Toml_RBDict_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "keyval"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 46, 78, 232, 161, 211, 209, 25)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ill-formed key-value pair syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "key"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 24, 166, 18, 184, 133, 165, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ill-formed key syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_Toml_RBDict_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inlineTable"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 125, 46, 131, 161, 142, 50, 23)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed inline table syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2_value;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3;
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_elabVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed value syntax"};
static const lean_object* l_Lake_Toml_elabVal___closed__0 = (const lean_object*)&l_Lake_Toml_elabVal___closed__0_value;
static lean_object* l_Lake_Toml_elabVal___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1;
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
x_18 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_Lean_instMonadExceptOfExceptionCoreM;
x_26 = l_Lean_Core_instMonadRefCoreM;
x_27 = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(x_7);
x_28 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_27, x_7);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
x_30 = l_Lean_Syntax_isLit_x3f(x_1, x_2);
if (lean_obj_tag(x_30) == 1)
{
uint8_t x_31; 
lean_dec_ref(x_29);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_ctor_set_tag(x_30, 0);
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_30);
x_34 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4));
x_35 = lean_string_append(x_34, x_3);
x_36 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5));
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = l_Lean_throwErrorAt___redArg(x_7, x_29, x_2, x_39);
x_41 = lean_apply_3(x_40, x_4, x_5, lean_box(0));
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = lean_ctor_get(x_9, 0);
x_43 = lean_ctor_get(x_9, 2);
x_44 = lean_ctor_get(x_9, 3);
x_45 = lean_ctor_get(x_9, 4);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_9);
x_46 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
x_47 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(x_42);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_48, 0, x_42);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_49, 0, x_42);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_51, 0, x_45);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_52, 0, x_44);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_53, 0, x_43);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set(x_54, 4, x_51);
lean_ctor_set(x_7, 1, x_47);
lean_ctor_set(x_7, 0, x_54);
x_55 = l_Lean_instMonadExceptOfExceptionCoreM;
x_56 = l_Lean_Core_instMonadRefCoreM;
x_57 = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(x_7);
x_58 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_57, x_7);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_58);
x_60 = l_Lean_Syntax_isLit_x3f(x_1, x_2);
if (lean_obj_tag(x_60) == 1)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_59);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_62;
 lean_ctor_set_tag(x_63, 0);
}
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_60);
x_64 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4));
x_65 = lean_string_append(x_64, x_3);
x_66 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5));
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = l_Lean_MessageData_ofFormat(x_68);
x_70 = l_Lean_throwErrorAt___redArg(x_7, x_59, x_2, x_69);
x_71 = lean_apply_3(x_70, x_4, x_5, lean_box(0));
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_72 = lean_ctor_get(x_7, 0);
lean_inc(x_72);
lean_dec(x_7);
x_73 = lean_ctor_get(x_72, 0);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_72, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 4);
lean_inc(x_76);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 x_77 = x_72;
} else {
 lean_dec_ref(x_72);
 x_77 = lean_box(0);
}
x_78 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
x_79 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(x_73);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_80, 0, x_73);
x_81 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_81, 0, x_73);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_83, 0, x_76);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_84, 0, x_75);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_85, 0, x_74);
if (lean_is_scalar(x_77)) {
 x_86 = lean_alloc_ctor(0, 5, 0);
} else {
 x_86 = x_77;
}
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_78);
lean_ctor_set(x_86, 2, x_85);
lean_ctor_set(x_86, 3, x_84);
lean_ctor_set(x_86, 4, x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_79);
x_88 = l_Lean_instMonadExceptOfExceptionCoreM;
x_89 = l_Lean_Core_instMonadRefCoreM;
x_90 = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(x_87);
x_91 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_90, x_87);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set(x_92, 2, x_91);
x_93 = l_Lean_Syntax_isLit_x3f(x_1, x_2);
if (lean_obj_tag(x_93) == 1)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_92);
lean_dec_ref(x_87);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 1, 0);
} else {
 x_96 = x_95;
 lean_ctor_set_tag(x_96, 0);
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_93);
x_97 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4));
x_98 = lean_string_append(x_97, x_3);
x_99 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5));
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_MessageData_ofFormat(x_101);
x_103 = l_Lean_throwErrorAt___redArg(x_87, x_92, x_2, x_102);
x_104 = lean_apply_3(x_103, x_4, x_5, lean_box(0));
return x_104;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2;
x_9 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__6;
lean_inc_ref(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(x_1, x_2, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 5);
x_8 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_3, 5, x_8);
x_9 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_ctor_get(x_3, 6);
x_17 = lean_ctor_get(x_3, 7);
x_18 = lean_ctor_get(x_3, 8);
x_19 = lean_ctor_get(x_3, 9);
x_20 = lean_ctor_get(x_3, 10);
x_21 = lean_ctor_get(x_3, 11);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*14);
x_23 = lean_ctor_get(x_3, 12);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_3, 13);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_26 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
x_27 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_12);
lean_ctor_set(x_27, 3, x_13);
lean_ctor_set(x_27, 4, x_14);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_16);
lean_ctor_set(x_27, 7, x_17);
lean_ctor_set(x_27, 8, x_18);
lean_ctor_set(x_27, 9, x_19);
lean_ctor_set(x_27, 10, x_20);
lean_ctor_set(x_27, 11, x_21);
lean_ctor_set(x_27, 12, x_23);
lean_ctor_set(x_27, 13, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*14 + 1, x_24);
x_28 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(x_2, x_27, x_4);
lean_dec_ref(x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5;
x_8 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_7, x_2, x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7));
lean_inc(x_10);
x_12 = l_Lean_Syntax_isOfKind(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9));
x_14 = l_Lean_Syntax_isOfKind(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5;
x_16 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_15, x_2, x_3);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = lean_box(x_12);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
x_19 = lean_box(x_12);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_next_fast(x_2, x_3);
x_10 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
x_11 = 95;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint32_t x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(10u);
x_14 = lean_nat_mul(x_4, x_13);
lean_dec(x_4);
x_15 = 48;
x_16 = lean_uint32_sub(x_10, x_15);
x_17 = lean_uint32_to_nat(x_16);
x_18 = lean_nat_add(x_14, x_17);
lean_dec(x_17);
lean_dec(x_14);
x_3 = x_9;
x_4 = x_18;
goto _start;
}
else
{
x_3 = x_9;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_positions(x_4);
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(x_4, x_1, x_5, x_2);
lean_dec_ref(x_1);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_String_Slice_Pos_get_x3f(x_28, x_26);
lean_dec_ref(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint32_t x_30; 
x_30 = 65;
x_2 = x_30;
goto block_25;
}
else
{
lean_object* x_31; uint32_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_unbox_uint32(x_31);
lean_dec(x_31);
x_2 = x_32;
goto block_25;
}
block_25:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 45;
x_4 = lean_uint32_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 43;
x_6 = lean_uint32_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_String_Slice_Pos_nextn(x_12, x_10, x_9);
lean_dec_ref(x_12);
x_14 = lean_string_utf8_extract(x_1, x_13, x_11);
lean_dec(x_13);
lean_dec_ref(x_1);
x_15 = lean_box(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_String_Slice_Pos_nextn(x_20, x_18, x_17);
lean_dec_ref(x_20);
x_22 = lean_string_utf8_extract(x_1, x_21, x_19);
lean_dec(x_21);
lean_dec_ref(x_1);
x_23 = lean_box(x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; uint32_t x_9; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = l_String_Slice_Pos_get_x3f(x_29, x_27);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint32_t x_31; 
x_31 = 65;
x_9 = x_31;
goto block_26;
}
else
{
lean_object* x_32; uint32_t x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_unbox_uint32(x_32);
lean_dec(x_32);
x_9 = x_33;
goto block_26;
}
block_8:
{
if (x_2 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(x_3);
x_5 = lean_nat_to_int(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(x_3);
x_7 = l_Int_negOfNat(x_6);
lean_dec(x_6);
return x_7;
}
}
block_26:
{
uint32_t x_10; uint8_t x_11; 
x_10 = 45;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 43;
x_13 = lean_uint32_dec_eq(x_9, x_12);
if (x_13 == 0)
{
x_2 = x_13;
x_3 = x_1;
goto block_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_String_Slice_Pos_nextn(x_17, x_15, x_14);
lean_dec_ref(x_17);
x_19 = lean_string_utf8_extract(x_1, x_18, x_16);
lean_dec(x_18);
lean_dec_ref(x_1);
x_2 = x_11;
x_3 = x_19;
goto block_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_String_Slice_Pos_nextn(x_23, x_21, x_20);
lean_dec_ref(x_23);
x_25 = lean_string_utf8_extract(x_1, x_24, x_22);
lean_dec(x_24);
lean_dec_ref(x_1);
x_2 = x_11;
x_3 = x_25;
goto block_8;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
x_11 = l_Lean_Syntax_isLit_x3f(x_10, x_1);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_5 = x_12;
x_6 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_11);
x_13 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4;
x_14 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_13, x_2, x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_string_utf8_next_fast(x_2, x_3);
x_12 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
x_13 = 95;
x_14 = lean_uint32_dec_eq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc(x_10);
lean_inc(x_9);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = 46;
x_19 = lean_uint32_dec_eq(x_12, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint32_t x_22; uint32_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_unsigned_to_nat(10u);
x_21 = lean_nat_mul(x_9, x_20);
lean_dec(x_9);
x_22 = 48;
x_23 = lean_uint32_sub(x_12, x_22);
x_24 = lean_uint32_to_nat(x_23);
x_25 = lean_nat_add(x_21, x_24);
lean_dec(x_24);
lean_dec(x_21);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_10, x_26);
lean_dec(x_10);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_25);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_29; 
lean_dec(x_10);
x_29 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_4, 1, x_29);
x_3 = x_11;
goto _start;
}
}
else
{
uint32_t x_31; uint8_t x_32; 
lean_dec(x_4);
x_31 = 46;
x_32 = lean_uint32_dec_eq(x_12, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint32_t x_35; uint32_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_unsigned_to_nat(10u);
x_34 = lean_nat_mul(x_9, x_33);
lean_dec(x_9);
x_35 = 48;
x_36 = lean_uint32_sub(x_12, x_35);
x_37 = lean_uint32_to_nat(x_36);
x_38 = lean_nat_add(x_34, x_37);
lean_dec(x_37);
lean_dec(x_34);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_10, x_39);
lean_dec(x_10);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_3 = x_11;
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_10);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_43);
x_3 = x_11;
x_4 = x_44;
goto _start;
}
}
}
else
{
x_3 = x_11;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_length(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_positions(x_6);
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(x_6, x_1, x_7, x_4);
lean_dec_ref(x_1);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_nat_dec_le(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_9);
return x_8;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_16 = x_4;
} else {
 lean_dec_ref(x_4);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_nat_sub(x_18, x_17);
x_20 = lean_nat_dec_eq(x_15, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint32_t x_31; uint32_t x_32; uint8_t x_33; 
x_21 = lean_string_utf8_next_fast(x_2, x_15);
x_31 = lean_string_utf8_get_fast(x_2, x_15);
x_32 = 69;
x_33 = lean_uint32_dec_eq(x_31, x_32);
if (x_33 == 0)
{
uint32_t x_34; uint8_t x_35; 
x_34 = 101;
x_35 = lean_uint32_dec_eq(x_31, x_34);
x_22 = x_35;
goto block_30;
}
else
{
x_22 = x_33;
goto block_30;
}
block_30:
{
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_15);
if (lean_is_scalar(x_16)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_16;
}
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_21);
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_1);
x_25 = l_String_Slice_slice_x21(x_1, x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (lean_is_scalar(x_16)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_16;
}
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_21);
x_27 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
lean_dec_ref(x_25);
x_6 = x_26;
x_7 = x_27;
x_8 = x_28;
x_9 = x_29;
goto block_13;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_16);
lean_dec(x_15);
x_36 = lean_box(1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_6 = x_36;
x_7 = x_2;
x_8 = x_14;
x_9 = x_3;
goto block_13;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_string_utf8_extract(x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_11 = lean_array_push(x_5, x_10);
x_4 = x_6;
x_5 = x_11;
goto _start;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object* x_1) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
x_7 = l_String_Slice_split___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(x_6);
x_8 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2;
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(x_6, x_1, x_5, x_7, x_8);
x_10 = lean_array_to_list(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = l_Int_negOfNat(x_15);
lean_dec(x_15);
lean_ctor_set(x_13, 1, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Int_negOfNat(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_11, 1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec_ref(x_10);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec_ref(x_11);
x_24 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(x_22);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(x_23);
x_28 = l_Int_negOfNat(x_26);
lean_dec(x_26);
x_29 = lean_int_add(x_28, x_27);
lean_dec(x_27);
lean_dec(x_28);
lean_ctor_set(x_24, 1, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(x_23);
x_33 = l_Int_negOfNat(x_31);
lean_dec(x_31);
x_34 = lean_int_add(x_33, x_32);
lean_dec(x_32);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_dec_ref(x_11);
lean_dec_ref(x_10);
goto block_3;
}
}
}
else
{
lean_dec(x_10);
goto block_3;
}
block_3:
{
lean_object* x_2; 
x_2 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1;
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
static double _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0));
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1));
x_8 = lean_string_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; double x_15; uint8_t x_16; 
x_9 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0;
x_13 = lean_int_dec_lt(x_11, x_12);
x_14 = lean_nat_abs(x_11);
lean_dec(x_11);
x_15 = l_Float_ofScientific(x_10, x_13, x_14);
lean_dec(x_10);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
if (x_16 == 0)
{
return x_15;
}
else
{
double x_17; 
x_17 = lean_float_negate(x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; double x_21; double x_22; double x_23; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Float_ofScientific(x_19, x_8, x_20);
x_22 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2;
x_23 = lean_float_div(x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; double x_26; double x_27; double x_28; double x_29; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Float_ofScientific(x_24, x_8, x_25);
x_27 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2;
x_28 = lean_float_div(x_26, x_27);
x_29 = lean_float_negate(x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
x_30 = lean_unbox(x_3);
lean_dec(x_3);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; double x_33; double x_34; double x_35; 
x_31 = lean_unsigned_to_nat(10u);
x_32 = lean_unsigned_to_nat(1u);
x_33 = l_Float_ofScientific(x_31, x_6, x_32);
x_34 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2;
x_35 = lean_float_div(x_33, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; double x_38; double x_39; double x_40; double x_41; 
x_36 = lean_unsigned_to_nat(10u);
x_37 = lean_unsigned_to_nat(1u);
x_38 = l_Float_ofScientific(x_36, x_6, x_37);
x_39 = lean_float_negate(x_38);
x_40 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2;
x_41 = lean_float_div(x_39, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object* x_1) {
_start:
{
double x_2; lean_object* x_3; 
x_2 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(x_1);
x_3 = lean_box_float(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
x_12 = l_Lean_Syntax_isLit_x3f(x_11, x_1);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_5 = x_13;
x_6 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_12);
x_14 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4;
x_15 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_14, x_2, x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
block_10:
{
double x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(x_5);
x_8 = lean_box_float(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_nat_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_10 = lean_nat_add(x_2, x_4);
lean_dec(x_4);
x_11 = lean_string_utf8_next_fast(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_2);
x_13 = lean_string_utf8_get_fast(x_3, x_10);
lean_dec(x_10);
x_14 = 95;
x_15 = lean_uint32_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint32_t x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_mul(x_5, x_16);
lean_dec(x_5);
x_18 = 48;
x_19 = lean_uint32_sub(x_13, x_18);
x_20 = lean_uint32_to_nat(x_19);
x_21 = lean_nat_add(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
x_4 = x_12;
x_5 = x_21;
goto _start;
}
else
{
x_4 = x_12;
goto _start;
}
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_17; lean_object* x_18; 
x_17 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
x_18 = l_Lean_Syntax_isLit_x3f(x_17, x_1);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_5 = x_19;
x_6 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_18);
x_20 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4;
x_21 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_20, x_2, x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_string_utf8_byte_size(x_5);
lean_inc_ref(x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_String_Slice_Pos_nextn(x_10, x_7, x_8);
lean_dec_ref(x_10);
lean_inc(x_11);
lean_inc_ref(x_5);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
x_13 = l_String_Slice_positions(x_12);
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(x_12, x_11, x_5, x_13, x_7);
lean_dec_ref(x_5);
lean_dec(x_11);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_nat_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_10 = lean_nat_add(x_2, x_4);
lean_dec(x_4);
x_11 = lean_string_utf8_next_fast(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_2);
x_13 = lean_string_utf8_get_fast(x_3, x_10);
lean_dec(x_10);
x_14 = 95;
x_15 = lean_uint32_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint32_t x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_unsigned_to_nat(8u);
x_17 = lean_nat_mul(x_5, x_16);
lean_dec(x_5);
x_18 = 48;
x_19 = lean_uint32_sub(x_13, x_18);
x_20 = lean_uint32_to_nat(x_19);
x_21 = lean_nat_add(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
x_4 = x_12;
x_5 = x_21;
goto _start;
}
else
{
x_4 = x_12;
goto _start;
}
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_17; lean_object* x_18; 
x_17 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
x_18 = l_Lean_Syntax_isLit_x3f(x_17, x_1);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_5 = x_19;
x_6 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_18);
x_20 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4;
x_21 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_20, x_2, x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_string_utf8_byte_size(x_5);
lean_inc_ref(x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_String_Slice_Pos_nextn(x_10, x_7, x_8);
lean_dec_ref(x_10);
lean_inc(x_11);
lean_inc_ref(x_5);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
x_13 = l_String_Slice_positions(x_12);
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(x_12, x_11, x_5, x_13, x_7);
lean_dec_ref(x_5);
lean_dec(x_11);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 57;
x_3 = lean_uint32_dec_le(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 70;
x_5 = lean_uint32_dec_le(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(10u);
x_7 = 97;
x_8 = lean_uint32_sub(x_1, x_7);
x_9 = lean_uint32_to_nat(x_8);
x_10 = lean_nat_add(x_6, x_9);
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; uint32_t x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(10u);
x_12 = 65;
x_13 = lean_uint32_sub(x_1, x_12);
x_14 = lean_uint32_to_nat(x_13);
x_15 = lean_nat_add(x_11, x_14);
lean_dec(x_14);
return x_15;
}
}
else
{
uint32_t x_16; uint32_t x_17; lean_object* x_18; 
x_16 = 48;
x_17 = lean_uint32_sub(x_1, x_16);
x_18 = lean_uint32_to_nat(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_nat_dec_eq(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_10 = lean_nat_add(x_2, x_4);
lean_dec(x_4);
x_11 = lean_string_utf8_next_fast(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_2);
x_13 = lean_string_utf8_get_fast(x_3, x_10);
lean_dec(x_10);
x_14 = 95;
x_15 = lean_uint32_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_nat_mul(x_5, x_16);
lean_dec(x_5);
x_18 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(x_13);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_4 = x_12;
x_5 = x_19;
goto _start;
}
else
{
x_4 = x_12;
goto _start;
}
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_17; lean_object* x_18; 
x_17 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
x_18 = l_Lean_Syntax_isLit_x3f(x_17, x_1);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_5 = x_19;
x_6 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_18);
x_20 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4;
x_21 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_20, x_2, x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
block_16:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_string_utf8_byte_size(x_5);
lean_inc_ref(x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_String_Slice_Pos_nextn(x_10, x_7, x_8);
lean_dec_ref(x_10);
lean_inc(x_11);
lean_inc_ref(x_5);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
x_13 = l_String_Slice_positions(x_12);
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(x_12, x_11, x_5, x_13, x_7);
lean_dec_ref(x_5);
lean_dec(x_11);
lean_dec_ref(x_12);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_14; lean_object* x_15; 
x_14 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
x_15 = l_Lean_Syntax_isLit_x3f(x_14, x_1);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_5 = x_16;
x_6 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_15);
x_17 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6;
x_18 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_17, x_2, x_3);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
block_13:
{
lean_object* x_7; 
x_7 = l_Lake_Toml_DateTime_ofString_x3f(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
lean_dec_ref(x_2);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 0);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
x_11 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1;
x_12 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_11, x_2, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_19; lean_object* x_20; 
x_19 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
x_20 = l_Lean_Syntax_isLit_x3f(x_19, x_1);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; 
lean_dec_ref(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_5 = x_21;
x_6 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
x_22 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4;
x_23 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_22, x_2, x_3);
return x_23;
}
block_18:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_5);
lean_inc_ref(x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_String_Slice_Pos_nextn(x_10, x_8, x_7);
lean_dec_ref(x_10);
lean_inc(x_11);
lean_inc_ref(x_5);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
x_13 = lean_nat_sub(x_9, x_11);
x_14 = l_String_Slice_Pos_prevn(x_12, x_13, x_7);
lean_dec_ref(x_12);
x_15 = lean_nat_add(x_11, x_14);
lean_dec(x_14);
x_16 = lean_string_utf8_extract(x_5, x_11, x_15);
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_5);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_instInhabitedSlice;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_nat_add(x_5, x_2);
lean_dec(x_2);
x_10 = lean_string_utf8_next_fast(x_4, x_9);
x_11 = lean_nat_sub(x_10, x_5);
x_12 = lean_string_utf8_get_fast(x_4, x_9);
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(16u);
x_14 = lean_nat_mul(x_3, x_13);
lean_dec(x_3);
x_15 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(x_12);
x_16 = lean_nat_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_2 = x_11;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1));
x_5 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_unsigned_to_nat(0u);
x_14 = lean_string_is_valid_pos(x_3, x_4);
if (x_14 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_13;
}
else
{
uint8_t x_15; 
x_15 = lean_string_is_valid_pos(x_3, x_5);
if (x_15 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_13;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_4, x_5);
if (x_16 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_13;
}
else
{
x_7 = x_1;
goto block_10;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_String_Slice_positions(x_7);
x_9 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(x_7, x_8, x_6);
lean_dec_ref(x_7);
return x_9;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3;
x_12 = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(x_11);
x_7 = x_12;
goto block_10;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_28; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_20 = lean_unsigned_to_nat(0u);
x_28 = lean_string_is_valid_pos(x_17, x_18);
if (x_28 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
goto block_27;
}
else
{
uint8_t x_29; 
x_29 = lean_string_is_valid_pos(x_17, x_19);
if (x_29 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
goto block_27;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_18, x_19);
if (x_30 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
goto block_27;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
x_21 = x_31;
goto block_24;
}
}
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_String_Slice_positions(x_21);
x_23 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(x_21, x_22, x_20);
lean_dec_ref(x_21);
return x_23;
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3;
x_26 = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(x_25);
x_21 = x_26;
goto block_24;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_42; 
x_42 = lean_string_utf8_at_end(x_1, x_2);
if (x_42 == 0)
{
uint32_t x_43; lean_object* x_44; uint32_t x_45; uint8_t x_46; 
x_43 = lean_string_utf8_get_fast(x_1, x_2);
x_44 = lean_string_utf8_next_fast(x_1, x_2);
lean_dec(x_2);
x_45 = 92;
x_46 = lean_uint32_dec_eq(x_43, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_string_push(x_3, x_43);
x_2 = x_44;
x_3 = x_47;
goto _start;
}
else
{
uint8_t x_49; 
x_49 = lean_string_utf8_at_end(x_1, x_44);
if (x_49 == 0)
{
uint32_t x_50; lean_object* x_51; uint32_t x_52; uint8_t x_53; 
x_50 = lean_string_utf8_get_fast(x_1, x_44);
x_51 = lean_string_utf8_next_fast(x_1, x_44);
x_52 = 98;
x_53 = lean_uint32_dec_eq(x_50, x_52);
if (x_53 == 0)
{
uint32_t x_54; uint8_t x_55; 
x_54 = 116;
x_55 = lean_uint32_dec_eq(x_50, x_54);
if (x_55 == 0)
{
uint32_t x_56; uint8_t x_57; 
x_56 = 110;
x_57 = lean_uint32_dec_eq(x_50, x_56);
if (x_57 == 0)
{
uint32_t x_58; uint8_t x_59; 
x_58 = 102;
x_59 = lean_uint32_dec_eq(x_50, x_58);
if (x_59 == 0)
{
uint32_t x_60; uint8_t x_61; 
x_60 = 114;
x_61 = lean_uint32_dec_eq(x_50, x_60);
if (x_61 == 0)
{
uint32_t x_62; uint8_t x_63; 
x_62 = 34;
x_63 = lean_uint32_dec_eq(x_50, x_62);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = lean_uint32_dec_eq(x_50, x_45);
if (x_64 == 0)
{
uint32_t x_65; uint8_t x_66; 
x_65 = 117;
x_66 = lean_uint32_dec_eq(x_50, x_65);
if (x_66 == 0)
{
uint32_t x_67; uint8_t x_68; 
x_67 = 85;
x_68 = lean_uint32_dec_eq(x_50, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_string_utf8_byte_size(x_1);
x_70 = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(x_1, x_69, x_44);
x_2 = x_70;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_51);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_unsigned_to_nat(8u);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Substring_Raw_nextn(x_73, x_74, x_75);
lean_dec_ref(x_73);
x_77 = lean_nat_add(x_51, x_76);
lean_dec(x_76);
lean_inc_ref(x_1);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_51);
lean_ctor_set(x_78, 2, x_77);
x_30 = x_78;
x_31 = x_4;
x_32 = x_5;
x_33 = lean_box(0);
goto block_41;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_51);
lean_ctor_set(x_80, 2, x_79);
x_81 = lean_unsigned_to_nat(4u);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Substring_Raw_nextn(x_80, x_81, x_82);
lean_dec_ref(x_80);
x_84 = lean_nat_add(x_51, x_83);
lean_dec(x_83);
lean_inc_ref(x_1);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_51);
lean_ctor_set(x_85, 2, x_84);
x_30 = x_85;
x_31 = x_4;
x_32 = x_5;
x_33 = lean_box(0);
goto block_41;
}
}
else
{
lean_object* x_86; 
x_86 = lean_string_push(x_3, x_45);
x_2 = x_51;
x_3 = x_86;
goto _start;
}
}
else
{
lean_object* x_88; 
x_88 = lean_string_push(x_3, x_62);
x_2 = x_51;
x_3 = x_88;
goto _start;
}
}
else
{
uint32_t x_90; lean_object* x_91; 
x_90 = 13;
x_91 = lean_string_push(x_3, x_90);
x_2 = x_51;
x_3 = x_91;
goto _start;
}
}
else
{
uint32_t x_93; lean_object* x_94; 
x_93 = 12;
x_94 = lean_string_push(x_3, x_93);
x_2 = x_51;
x_3 = x_94;
goto _start;
}
}
else
{
uint32_t x_96; lean_object* x_97; 
x_96 = 10;
x_97 = lean_string_push(x_3, x_96);
x_2 = x_51;
x_3 = x_97;
goto _start;
}
}
else
{
uint32_t x_99; lean_object* x_100; 
x_99 = 9;
x_100 = lean_string_push(x_3, x_99);
x_2 = x_51;
x_3 = x_100;
goto _start;
}
}
else
{
uint32_t x_102; lean_object* x_103; 
x_102 = 8;
x_103 = lean_string_push(x_3, x_102);
x_2 = x_51;
x_3 = x_103;
goto _start;
}
}
else
{
lean_object* x_105; 
lean_dec_ref(x_1);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_3);
return x_105;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_3);
return x_106;
}
block_19:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1;
x_12 = lean_substring_tostring(x_8);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_MessageData_ofFormat(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(x_17, x_9, x_7);
return x_18;
}
block_29:
{
lean_object* x_25; uint32_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
lean_dec_ref(x_21);
x_26 = lean_uint32_of_nat(x_22);
lean_dec(x_22);
x_27 = lean_string_push(x_3, x_26);
x_2 = x_25;
x_3 = x_27;
x_4 = x_23;
x_5 = x_20;
goto _start;
}
block_41:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_inc_ref(x_30);
x_34 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(x_30);
x_35 = lean_unsigned_to_nat(55296u);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_unsigned_to_nat(57343u);
x_38 = lean_nat_dec_lt(x_37, x_34);
if (x_38 == 0)
{
lean_dec(x_34);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = x_32;
x_8 = x_30;
x_9 = x_31;
x_10 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1114112u);
x_40 = lean_nat_dec_lt(x_34, x_39);
if (x_40 == 0)
{
lean_dec(x_34);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = x_32;
x_8 = x_30;
x_9 = x_31;
x_10 = lean_box(0);
goto block_19;
}
else
{
x_20 = x_32;
x_21 = x_30;
x_22 = x_34;
x_23 = x_31;
x_24 = lean_box(0);
goto block_29;
}
}
}
else
{
x_20 = x_32;
x_21 = x_30;
x_22 = x_34;
x_23 = x_31;
x_24 = lean_box(0);
goto block_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_7;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_50; lean_object* x_51; 
x_50 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
x_51 = l_Lean_Syntax_isLit_x3f(x_50, x_1);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_5 = x_52;
x_6 = lean_box(0);
goto block_49;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5;
x_54 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_53, x_2, x_3);
return x_54;
}
block_49:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_byte_size(x_5);
lean_inc_ref(x_5);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_String_Slice_Pos_nextn(x_9, x_7, x_12);
lean_dec_ref(x_9);
lean_inc(x_13);
lean_inc_ref(x_5);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_8);
x_15 = lean_nat_sub(x_8, x_13);
x_16 = l_String_Slice_Pos_prevn(x_14, x_15, x_12);
lean_dec_ref(x_14);
x_17 = lean_nat_add(x_13, x_16);
lean_dec(x_16);
x_18 = lean_string_utf8_extract(x_5, x_13, x_17);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_5);
x_19 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
x_20 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_2, 5, x_20);
x_21 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(x_18, x_7, x_19, x_2, x_3);
lean_dec_ref(x_2);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
x_26 = lean_ctor_get(x_2, 4);
x_27 = lean_ctor_get(x_2, 5);
x_28 = lean_ctor_get(x_2, 6);
x_29 = lean_ctor_get(x_2, 7);
x_30 = lean_ctor_get(x_2, 8);
x_31 = lean_ctor_get(x_2, 9);
x_32 = lean_ctor_get(x_2, 10);
x_33 = lean_ctor_get(x_2, 11);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*14);
x_35 = lean_ctor_get(x_2, 12);
x_36 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
x_37 = lean_ctor_get(x_2, 13);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_String_Slice_Pos_nextn(x_9, x_7, x_38);
lean_dec_ref(x_9);
lean_inc(x_39);
lean_inc_ref(x_5);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_8);
x_41 = lean_nat_sub(x_8, x_39);
x_42 = l_String_Slice_Pos_prevn(x_40, x_41, x_38);
lean_dec_ref(x_40);
x_43 = lean_nat_add(x_39, x_42);
lean_dec(x_42);
x_44 = lean_string_utf8_extract(x_5, x_39, x_43);
lean_dec(x_43);
lean_dec(x_39);
lean_dec_ref(x_5);
x_45 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
x_46 = l_Lean_replaceRef(x_1, x_27);
lean_dec(x_27);
x_47 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_47, 0, x_22);
lean_ctor_set(x_47, 1, x_23);
lean_ctor_set(x_47, 2, x_24);
lean_ctor_set(x_47, 3, x_25);
lean_ctor_set(x_47, 4, x_26);
lean_ctor_set(x_47, 5, x_46);
lean_ctor_set(x_47, 6, x_28);
lean_ctor_set(x_47, 7, x_29);
lean_ctor_set(x_47, 8, x_30);
lean_ctor_set(x_47, 9, x_31);
lean_ctor_set(x_47, 10, x_32);
lean_ctor_set(x_47, 11, x_33);
lean_ctor_set(x_47, 12, x_35);
lean_ctor_set(x_47, 13, x_37);
lean_ctor_set_uint8(x_47, sizeof(void*)*14, x_34);
lean_ctor_set_uint8(x_47, sizeof(void*)*14 + 1, x_36);
x_48 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(x_44, x_7, x_45, x_47, x_3);
lean_dec_ref(x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_String_Slice_Pos_get_x3f(x_22, x_20);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint32_t x_24; 
x_24 = 65;
x_2 = x_24;
goto block_19;
}
else
{
lean_object* x_25; uint32_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_unbox_uint32(x_25);
lean_dec(x_25);
x_2 = x_26;
goto block_19;
}
block_19:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 13;
x_4 = lean_uint32_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 10;
x_6 = lean_uint32_dec_eq(x_2, x_5);
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_String_Slice_Pos_nextn(x_10, x_8, x_7);
lean_dec_ref(x_10);
x_12 = lean_string_utf8_extract(x_1, x_11, x_9);
lean_dec(x_11);
lean_dec_ref(x_1);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_String_Slice_Pos_nextn(x_16, x_14, x_13);
lean_dec_ref(x_16);
x_18 = lean_string_utf8_extract(x_1, x_17, x_15);
lean_dec(x_17);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_20; lean_object* x_21; 
x_20 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
x_21 = l_Lean_Syntax_isLit_x3f(x_20, x_1);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; 
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_5 = x_22;
x_6 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
x_23 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4;
x_24 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_23, x_2, x_3);
return x_24;
}
block_19:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_5);
lean_inc_ref(x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_String_Slice_Pos_nextn(x_10, x_8, x_7);
lean_dec_ref(x_10);
lean_inc(x_11);
lean_inc_ref(x_5);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
x_13 = lean_nat_sub(x_9, x_11);
x_14 = l_String_Slice_Pos_prevn(x_12, x_13, x_7);
lean_dec_ref(x_12);
x_15 = lean_nat_add(x_11, x_14);
lean_dec(x_14);
x_16 = lean_string_utf8_extract(x_5, x_11, x_15);
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_5);
x_17 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_52; lean_object* x_53; 
x_52 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
x_53 = l_Lean_Syntax_isLit_x3f(x_52, x_1);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_5 = x_54;
x_6 = lean_box(0);
goto block_51;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
x_55 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4;
x_56 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_55, x_2, x_3);
return x_56;
}
block_51:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_byte_size(x_5);
lean_inc_ref(x_5);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_String_Slice_Pos_nextn(x_9, x_7, x_12);
lean_dec_ref(x_9);
lean_inc(x_13);
lean_inc_ref(x_5);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_8);
x_15 = lean_nat_sub(x_8, x_13);
x_16 = l_String_Slice_Pos_prevn(x_14, x_15, x_12);
lean_dec_ref(x_14);
x_17 = lean_nat_add(x_13, x_16);
lean_dec(x_16);
x_18 = lean_string_utf8_extract(x_5, x_13, x_17);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_5);
x_19 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(x_18);
x_20 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
x_21 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_2, 5, x_21);
x_22 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(x_19, x_7, x_20, x_2, x_3);
lean_dec_ref(x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
x_27 = lean_ctor_get(x_2, 4);
x_28 = lean_ctor_get(x_2, 5);
x_29 = lean_ctor_get(x_2, 6);
x_30 = lean_ctor_get(x_2, 7);
x_31 = lean_ctor_get(x_2, 8);
x_32 = lean_ctor_get(x_2, 9);
x_33 = lean_ctor_get(x_2, 10);
x_34 = lean_ctor_get(x_2, 11);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*14);
x_36 = lean_ctor_get(x_2, 12);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*14 + 1);
x_38 = lean_ctor_get(x_2, 13);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_39 = lean_unsigned_to_nat(3u);
x_40 = l_String_Slice_Pos_nextn(x_9, x_7, x_39);
lean_dec_ref(x_9);
lean_inc(x_40);
lean_inc_ref(x_5);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_8);
x_42 = lean_nat_sub(x_8, x_40);
x_43 = l_String_Slice_Pos_prevn(x_41, x_42, x_39);
lean_dec_ref(x_41);
x_44 = lean_nat_add(x_40, x_43);
lean_dec(x_43);
x_45 = lean_string_utf8_extract(x_5, x_40, x_44);
lean_dec(x_44);
lean_dec(x_40);
lean_dec_ref(x_5);
x_46 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(x_45);
x_47 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
x_48 = l_Lean_replaceRef(x_1, x_28);
lean_dec(x_28);
x_49 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_24);
lean_ctor_set(x_49, 2, x_25);
lean_ctor_set(x_49, 3, x_26);
lean_ctor_set(x_49, 4, x_27);
lean_ctor_set(x_49, 5, x_48);
lean_ctor_set(x_49, 6, x_29);
lean_ctor_set(x_49, 7, x_30);
lean_ctor_set(x_49, 8, x_31);
lean_ctor_set(x_49, 9, x_32);
lean_ctor_set(x_49, 10, x_33);
lean_ctor_set(x_49, 11, x_34);
lean_ctor_set(x_49, 12, x_36);
lean_ctor_set(x_49, 13, x_38);
lean_ctor_set_uint8(x_49, sizeof(void*)*14, x_35);
lean_ctor_set_uint8(x_49, sizeof(void*)*14 + 1, x_37);
x_50 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(x_46, x_7, x_47, x_49, x_3);
lean_dec_ref(x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3;
x_8 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_7, x_2, x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(x_10);
x_12 = l_Lean_Syntax_isOfKind(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(x_10);
x_14 = l_Lean_Syntax_isOfKind(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
lean_inc(x_10);
x_16 = l_Lean_Syntax_isOfKind(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
lean_inc(x_10);
x_18 = l_Lean_Syntax_isOfKind(x_10, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_19 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3;
x_20 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_19, x_2, x_3);
lean_dec(x_1);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(x_10, x_2, x_3);
lean_dec(x_10);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(x_10, x_2, x_3);
lean_dec(x_10);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(x_10, x_2, x_3);
lean_dec(x_10);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(x_10, x_2, x_3);
lean_dec(x_10);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1;
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 2);
x_12 = lean_ctor_get(x_7, 3);
x_13 = lean_ctor_get(x_7, 4);
x_14 = lean_ctor_get(x_7, 1);
lean_dec(x_14);
x_15 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
x_16 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
x_17 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(x_10);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_10);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_12);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_23, 0, x_11);
lean_ctor_set(x_7, 4, x_21);
lean_ctor_set(x_7, 3, x_22);
lean_ctor_set(x_7, 2, x_23);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_20);
lean_ctor_set(x_5, 1, x_17);
x_24 = l_Lean_instMonadExceptOfExceptionCoreM;
x_25 = l_Lean_Core_instMonadRefCoreM;
x_26 = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(x_5);
x_27 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_26, x_5);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Lean_Syntax_isLit_x3f(x_15, x_1);
if (lean_obj_tag(x_29) == 1)
{
uint8_t x_30; 
lean_dec_ref(x_28);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_ctor_set_tag(x_29, 0);
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
x_33 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4;
x_34 = l_Lean_throwErrorAt___redArg(x_5, x_28, x_1, x_33);
x_35 = lean_apply_3(x_34, x_2, x_3, lean_box(0));
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 2);
x_38 = lean_ctor_get(x_7, 3);
x_39 = lean_ctor_get(x_7, 4);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_40 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
x_41 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
x_42 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(x_36);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_36);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_39);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_47, 0, x_38);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_48, 0, x_37);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set(x_49, 4, x_46);
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_49);
x_50 = l_Lean_instMonadExceptOfExceptionCoreM;
x_51 = l_Lean_Core_instMonadRefCoreM;
x_52 = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(x_5);
x_53 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_52, x_5);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_53);
x_55 = l_Lean_Syntax_isLit_x3f(x_40, x_1);
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_54);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 1, 0);
} else {
 x_58 = x_57;
 lean_ctor_set_tag(x_58, 0);
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_55);
x_59 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4;
x_60 = l_Lean_throwErrorAt___redArg(x_5, x_54, x_1, x_59);
x_61 = lean_apply_3(x_60, x_2, x_3, lean_box(0));
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_62 = lean_ctor_get(x_5, 0);
lean_inc(x_62);
lean_dec(x_5);
x_63 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_62, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 4);
lean_inc(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
 x_67 = lean_box(0);
}
x_68 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
x_69 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
x_70 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(x_63);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_71, 0, x_63);
x_72 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_72, 0, x_63);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_74, 0, x_66);
x_75 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_75, 0, x_65);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_76, 0, x_64);
if (lean_is_scalar(x_67)) {
 x_77 = lean_alloc_ctor(0, 5, 0);
} else {
 x_77 = x_67;
}
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_75);
lean_ctor_set(x_77, 4, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
x_79 = l_Lean_instMonadExceptOfExceptionCoreM;
x_80 = l_Lean_Core_instMonadRefCoreM;
x_81 = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(x_78);
x_82 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_81, x_78);
x_83 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_82);
x_84 = l_Lean_Syntax_isLit_x3f(x_68, x_1);
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_83);
lean_dec_ref(x_78);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 1, 0);
} else {
 x_87 = x_86;
 lean_ctor_set_tag(x_87, 0);
}
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_84);
x_88 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4;
x_89 = l_Lean_throwErrorAt___redArg(x_78, x_83, x_1, x_88);
x_90 = lean_apply_3(x_89, x_2, x_3, lean_box(0));
return x_90;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_elabSimpleKey___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lake_Toml_elabSimpleKey___closed__3;
x_8 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_7, x_2, x_3);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
lean_inc(x_10);
x_12 = l_Lean_Syntax_isOfKind(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(x_10);
x_14 = l_Lean_Syntax_isOfKind(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(x_10);
x_16 = l_Lean_Syntax_isOfKind(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_17 = l_Lake_Toml_elabSimpleKey___closed__3;
x_18 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_17, x_2, x_3);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(x_10, x_2, x_3);
lean_dec(x_10);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(x_10, x_2, x_3);
lean_dec(x_10);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = l_Lean_Syntax_isLit_x3f(x_11, x_10);
if (lean_obj_tag(x_21) == 1)
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec_ref(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_ctor_set_tag(x_21, 0);
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
x_25 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4;
x_26 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_10, x_25, x_2, x_3);
lean_dec(x_10);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Toml_elabSimpleKey(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_4, x_3);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
x_11 = lean_apply_4(x_1, x_10, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_14, x_3, x_12);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(x_1, x_8, x_9, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_2);
x_8 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3;
x_9 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_8, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = l_Lean_Syntax_TSepArray_getElems___redArg(x_12);
lean_dec_ref(x_12);
x_14 = lean_array_size(x_13);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(x_2, x_14, x_15, x_13, x_3, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(x_1, x_2, x_9, x_10, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(x_1, x_2, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 5);
x_9 = l_Lean_replaceRef(x_1, x_8);
lean_dec(x_8);
lean_ctor_set(x_4, 5, x_9);
x_10 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(x_2, x_4, x_5);
lean_dec_ref(x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_4, 6);
x_18 = lean_ctor_get(x_4, 7);
x_19 = lean_ctor_get(x_4, 8);
x_20 = lean_ctor_get(x_4, 9);
x_21 = lean_ctor_get(x_4, 10);
x_22 = lean_ctor_get(x_4, 11);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*14);
x_24 = lean_ctor_get(x_4, 12);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*14 + 1);
x_26 = lean_ctor_get(x_4, 13);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_27 = l_Lean_replaceRef(x_1, x_16);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_12);
lean_ctor_set(x_28, 2, x_13);
lean_ctor_set(x_28, 3, x_14);
lean_ctor_set(x_28, 4, x_15);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_17);
lean_ctor_set(x_28, 7, x_18);
lean_ctor_set(x_28, 8, x_19);
lean_ctor_set(x_28, 9, x_20);
lean_ctor_set(x_28, 10, x_21);
lean_ctor_set(x_28, 11, x_22);
lean_ctor_set(x_28, 12, x_24);
lean_ctor_set(x_28, 13, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*14, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*14 + 1, x_25);
x_29 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(x_2, x_28, x_5);
lean_dec_ref(x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_4, x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_uget(x_3, x_4);
lean_inc_ref(x_8);
lean_inc(x_19);
x_20 = l_Lake_Toml_elabSimpleKey(x_19, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_36; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
x_23 = l_Lean_Name_str___override(x_6, x_21);
lean_inc_ref(x_1);
lean_inc(x_23);
x_36 = l_Lake_Toml_RBDict_findEntry_x3f___redArg(x_22, x_23, x_1);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_19);
x_37 = lean_box(0);
lean_inc(x_23);
x_38 = l_Lake_Toml_RBDict_push___redArg(x_22, x_23, x_37, x_7);
x_11 = x_23;
x_12 = x_38;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec_ref(x_36);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
if (x_2 == 0)
{
goto block_35;
}
else
{
lean_dec(x_19);
x_11 = x_23;
x_12 = x_7;
x_13 = lean_box(0);
goto block_17;
}
}
else
{
lean_dec_ref(x_40);
goto block_35;
}
}
block_35:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2;
lean_inc(x_23);
x_25 = l_Lean_MessageData_ofName(x_23);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_inc_ref(x_8);
x_29 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(x_19, x_28, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_11 = x_23;
x_12 = x_31;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_32; 
lean_dec(x_23);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_20, 0);
lean_inc(x_42);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_7);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_6 = x_11;
x_7 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(x_1, x_11, x_3, x_12, x_13, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
x_16 = lean_box(x_1);
lean_ctor_set(x_5, 0, x_16);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_box(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_6 = x_19;
goto block_10;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_ctor_get(x_5, 0);
lean_dec(x_22);
x_23 = lean_array_uget(x_2, x_3);
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_box(x_11);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_25);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_array_uget(x_2, x_3);
x_28 = lean_array_push(x_26, x_27);
x_29 = lean_box(x_11);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_6 = x_30;
goto block_10;
}
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(x_6, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_15; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_3, x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1));
x_20 = lean_array_uget(x_2, x_3);
lean_inc(x_20);
x_21 = l_Lean_Syntax_isOfKind(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_5);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3;
lean_inc_ref(x_6);
x_23 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_20, x_22, x_6, x_7);
lean_dec(x_20);
x_15 = x_23;
goto block_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_20, x_24);
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5));
lean_inc(x_25);
x_27 = l_Lean_Syntax_isOfKind(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
lean_dec_ref(x_5);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7;
lean_inc_ref(x_6);
x_29 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_25, x_28, x_6, x_7);
lean_dec(x_25);
x_15 = x_29;
goto block_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_58; lean_object* x_59; lean_object* x_67; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_30 = lean_unsigned_to_nat(2u);
x_31 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
x_32 = l_Lean_Syntax_getArg(x_20, x_30);
lean_dec(x_20);
x_86 = l_Lean_Syntax_getArg(x_25, x_24);
x_87 = l_Lean_Syntax_getArgs(x_86);
lean_dec(x_86);
x_88 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8;
x_89 = lean_array_get_size(x_87);
x_90 = lean_nat_dec_lt(x_24, x_89);
if (x_90 == 0)
{
lean_dec_ref(x_87);
x_67 = x_88;
goto block_85;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_box(x_27);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
x_93 = lean_nat_dec_le(x_89, x_89);
if (x_93 == 0)
{
if (x_90 == 0)
{
lean_dec_ref(x_92);
lean_dec_ref(x_87);
x_67 = x_88;
goto block_85;
}
else
{
size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; 
x_94 = 0;
x_95 = lean_usize_of_nat(x_89);
x_96 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(x_27, x_87, x_94, x_95, x_92);
lean_dec_ref(x_87);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec_ref(x_96);
x_67 = x_97;
goto block_85;
}
}
else
{
size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; 
x_98 = 0;
x_99 = lean_usize_of_nat(x_89);
x_100 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(x_27, x_87, x_98, x_99, x_92);
lean_dec_ref(x_87);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec_ref(x_100);
x_67 = x_101;
goto block_85;
}
}
block_57:
{
lean_object* x_37; 
lean_inc_ref(x_6);
lean_inc(x_33);
x_37 = l_Lake_Toml_elabSimpleKey(x_33, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_Name_str___override(x_34, x_38);
lean_inc_ref(x_35);
lean_inc(x_39);
x_40 = l_Lake_Toml_RBDict_contains___redArg(x_31, x_39, x_35);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_33);
lean_inc_ref(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
x_41 = lean_apply_4(x_1, x_32, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lake_Toml_RBDict_push___redArg(x_31, x_39, x_43, x_35);
x_9 = x_44;
x_10 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_45; 
lean_dec(x_39);
lean_dec_ref(x_35);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_35);
lean_dec(x_32);
x_48 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2;
x_49 = l_Lean_MessageData_ofName(x_39);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_inc_ref(x_6);
x_53 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_33, x_52, x_6, x_7);
lean_dec(x_33);
x_15 = x_53;
goto block_17;
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_37);
if (x_54 == 0)
{
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_37, 0);
lean_inc(x_55);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
block_66:
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_33 = x_58;
x_34 = x_61;
x_35 = x_62;
x_36 = lean_box(0);
goto block_57;
}
else
{
uint8_t x_63; 
lean_dec(x_58);
lean_dec(x_32);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
block_85:
{
size_t x_68; size_t x_69; lean_object* x_70; 
x_68 = lean_array_size(x_67);
x_69 = 0;
x_70 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(x_68, x_69, x_67);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_32);
lean_dec_ref(x_5);
x_71 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7;
lean_inc_ref(x_6);
x_72 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_25, x_71, x_6, x_7);
lean_dec(x_25);
x_15 = x_72;
goto block_17;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_25);
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec_ref(x_70);
x_74 = lean_box(0);
x_75 = l_Array_back_x21___redArg(x_74, x_73);
x_76 = lean_box(0);
x_77 = lean_array_pop(x_73);
x_78 = lean_array_get_size(x_77);
x_79 = lean_nat_dec_lt(x_24, x_78);
if (x_79 == 0)
{
lean_dec_ref(x_77);
x_33 = x_75;
x_34 = x_76;
x_35 = x_5;
x_36 = lean_box(0);
goto block_57;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_78, x_78);
if (x_80 == 0)
{
if (x_79 == 0)
{
lean_dec_ref(x_77);
x_33 = x_75;
x_34 = x_76;
x_35 = x_5;
x_36 = lean_box(0);
goto block_57;
}
else
{
size_t x_81; lean_object* x_82; 
x_81 = lean_usize_of_nat(x_78);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_82 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(x_5, x_27, x_77, x_69, x_81, x_76, x_5, x_6, x_7);
lean_dec_ref(x_77);
x_58 = x_75;
x_59 = x_82;
goto block_66;
}
}
else
{
size_t x_83; lean_object* x_84; 
x_83 = lean_usize_of_nat(x_78);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(x_5, x_27, x_77, x_69, x_83, x_76, x_5, x_6, x_7);
lean_dec_ref(x_77);
x_58 = x_75;
x_59 = x_84;
goto block_66;
}
}
}
}
}
}
}
else
{
lean_object* x_102; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_5);
return x_102;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_9;
goto _start;
}
block_17:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_9 = x_16;
x_10 = lean_box(0);
goto block_14;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(x_1, x_2, x_9, x_10, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
x_16 = l_Lake_Toml_RBDict_push___redArg(x_15, x_13, x_14, x_4);
x_5 = x_16;
goto block_9;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
x_2 = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
x_2 = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_2);
x_8 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3;
x_9 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_8, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_32; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_38 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5;
x_39 = l_Lean_Syntax_TSepArray_getElems___redArg(x_13);
lean_dec_ref(x_13);
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_lt(x_10, x_40);
if (x_41 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_14 = x_38;
x_15 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_40, x_40);
if (x_42 == 0)
{
if (x_41 == 0)
{
lean_dec_ref(x_39);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_14 = x_38;
x_15 = lean_box(0);
goto block_31;
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_usize_of_nat(x_40);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(x_2, x_39, x_43, x_44, x_38, x_3, x_4);
lean_dec_ref(x_39);
x_32 = x_45;
goto block_37;
}
}
else
{
size_t x_46; size_t x_47; lean_object* x_48; 
x_46 = 0;
x_47 = lean_usize_of_nat(x_40);
x_48 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(x_2, x_39, x_46, x_47, x_38, x_3, x_4);
lean_dec_ref(x_39);
x_32 = x_48;
goto block_37;
}
}
block_31:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_14);
x_17 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4;
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_10, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_16);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_18, x_18);
if (x_21 == 0)
{
if (x_19 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_16);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_17);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_18);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(x_16, x_23, x_24, x_17);
lean_dec_ref(x_16);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_18);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(x_16, x_27, x_28, x_17);
lean_dec_ref(x_16);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
block_37:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_14 = x_33;
x_15 = lean_box(0);
goto block_31;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(x_2, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
static lean_object* _init_l_Lake_Toml_elabVal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_Toml_elabVal___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Toml_elabVal(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
lean_inc(x_1);
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
lean_inc(x_1);
x_10 = l_Lean_Syntax_isOfKind(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
lean_inc(x_1);
x_14 = l_Lean_Syntax_isOfKind(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(x_1);
x_18 = l_Lean_Syntax_isOfKind(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(x_1);
x_20 = l_Lean_Syntax_isOfKind(x_1, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(x_1);
x_22 = l_Lean_Syntax_isOfKind(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(x_1);
x_24 = l_Lean_Syntax_isOfKind(x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lake_Toml_elabVal___closed__1;
x_26 = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(x_1, x_25, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(x_1);
x_28 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(x_1, x_27, x_2, x_3);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(x_1);
x_39 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(x_1, x_38, x_2, x_3);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; 
lean_inc(x_1);
x_49 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(x_1, x_2, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_52, 0, x_1);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_53);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(x_55, 0, x_1);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_49);
if (x_58 == 0)
{
return x_49;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
lean_dec(x_49);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; 
lean_inc(x_1);
x_61 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(x_1, x_2, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
lean_dec(x_61);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; 
x_71 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(x_1, x_2, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_71);
if (x_78 == 0)
{
return x_71;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_71, 0);
lean_inc(x_79);
lean_dec(x_71);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(x_1, x_2, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_nat_to_int(x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_81, 0, x_85);
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
lean_dec(x_81);
x_87 = lean_nat_to_int(x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_81);
if (x_90 == 0)
{
return x_81;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
lean_dec(x_81);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
}
else
{
lean_object* x_93; 
x_93 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(x_1, x_2, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_nat_to_int(x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_93, 0, x_97);
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_nat_to_int(x_98);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_93);
if (x_102 == 0)
{
return x_93;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_93, 0);
lean_inc(x_103);
lean_dec(x_93);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; 
x_105 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(x_1, x_2, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_nat_to_int(x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_105, 0, x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_nat_to_int(x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_105);
if (x_114 == 0)
{
return x_105;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_105, 0);
lean_inc(x_115);
lean_dec(x_105);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
}
else
{
lean_object* x_117; 
x_117 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(x_1, x_2, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_117, 0, x_120);
return x_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
lean_dec(x_117);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
uint8_t x_124; 
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_117);
if (x_124 == 0)
{
return x_117;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_117, 0);
lean_inc(x_125);
lean_dec(x_117);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
}
else
{
lean_object* x_127; 
x_127 = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(x_1, x_2, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; double x_131; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(x_130, 0, x_1);
x_131 = lean_unbox_float(x_129);
lean_dec(x_129);
lean_ctor_set_float(x_130, sizeof(void*)*1, x_131);
lean_ctor_set(x_127, 0, x_130);
return x_127;
}
else
{
lean_object* x_132; lean_object* x_133; double x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(x_133, 0, x_1);
x_134 = lean_unbox_float(x_132);
lean_dec(x_132);
lean_ctor_set_float(x_133, sizeof(void*)*1, x_134);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_133);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_127);
if (x_136 == 0)
{
return x_127;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_127, 0);
lean_inc(x_137);
lean_dec(x_127);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
}
}
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__6 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__6);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2();
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
l_Lake_Toml_elabSimpleKey___closed__3 = _init_l_Lake_Toml_elabSimpleKey___closed__3();
lean_mark_persistent(l_Lake_Toml_elabSimpleKey___closed__3);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5 = _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5);
l_Lake_Toml_elabVal___closed__1 = _init_l_Lake_Toml_elabVal___closed__1();
lean_mark_persistent(l_Lake_Toml_elabVal___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
