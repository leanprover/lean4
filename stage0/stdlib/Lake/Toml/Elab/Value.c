// Lean compiler output
// Module: Lake.Toml.Elab.Value
// Imports: public import Lake.Toml.Data.Value public import Lake.Toml.Grammar meta import all Lake.Toml.Grammar
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_substring_tostring(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_positions(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lake_Toml_RBDict_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_Toml_RBDict_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_negate(double);
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
extern lean_object* l_Lean_Core_instMonadRefCoreM;
extern lean_object* l_Lean_Core_instAddMessageContextCoreM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1;
static const lean_closure_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value;
static const lean_closure_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ill-formed "};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Toml"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "boolean"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 74, 28, 167, 158, 175, 30, 0)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invalid boolean"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object*);
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1;
static const lean_array_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inf"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nan"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2;
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "invalid date-time"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6;
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid unicode escape `"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
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
static lean_once_cell_t l_Lake_Toml_elabSimpleKey___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_elabSimpleKey___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3;
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
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cannot redefine key `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "key"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 24, 166, 18, 184, 133, 165, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ill-formed key syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_elabVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed value syntax"};
static const lean_object* l_Lake_Toml_elabVal___closed__0 = (const lean_object*)&l_Lake_Toml_elabVal___closed__0_value;
static lean_once_cell_t l_Lake_Toml_elabVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_elabVal___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO(lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0);
v___x_3_ = l_StateRefT_x27_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(lean_object* v_k_8_, lean_object* v_x_9_, lean_object* v_name_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; lean_object* v_toApplicative_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_64_; 
v___x_14_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_15_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_64_ == 0)
{
lean_object* v_unused_65_; 
v_unused_65_ = lean_ctor_get(v___x_14_, 1);
lean_dec(v_unused_65_);
v___x_17_ = v___x_14_;
v_isShared_18_ = v_isSharedCheck_64_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_toApplicative_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_64_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v_toFunctor_19_; lean_object* v_toSeq_20_; lean_object* v_toSeqLeft_21_; lean_object* v_toSeqRight_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_62_; 
v_toFunctor_19_ = lean_ctor_get(v_toApplicative_15_, 0);
v_toSeq_20_ = lean_ctor_get(v_toApplicative_15_, 2);
v_toSeqLeft_21_ = lean_ctor_get(v_toApplicative_15_, 3);
v_toSeqRight_22_ = lean_ctor_get(v_toApplicative_15_, 4);
v_isSharedCheck_62_ = !lean_is_exclusive(v_toApplicative_15_);
if (v_isSharedCheck_62_ == 0)
{
lean_object* v_unused_63_; 
v_unused_63_ = lean_ctor_get(v_toApplicative_15_, 1);
lean_dec(v_unused_63_);
v___x_24_ = v_toApplicative_15_;
v_isShared_25_ = v_isSharedCheck_62_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_toSeqRight_22_);
lean_inc(v_toSeqLeft_21_);
lean_inc(v_toSeq_20_);
lean_inc(v_toFunctor_19_);
lean_dec(v_toApplicative_15_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_62_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___f_28_; lean_object* v___f_29_; lean_object* v___x_30_; lean_object* v___f_31_; lean_object* v___f_32_; lean_object* v___f_33_; lean_object* v___x_35_; 
v___f_26_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_27_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(v_toFunctor_19_);
v___f_28_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_28_, 0, v_toFunctor_19_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_29_, 0, v_toFunctor_19_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___f_28_);
lean_ctor_set(v___x_30_, 1, v___f_29_);
v___f_31_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_31_, 0, v_toSeqRight_22_);
v___f_32_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_32_, 0, v_toSeqLeft_21_);
v___f_33_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_33_, 0, v_toSeq_20_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 4, v___f_31_);
lean_ctor_set(v___x_24_, 3, v___f_32_);
lean_ctor_set(v___x_24_, 2, v___f_33_);
lean_ctor_set(v___x_24_, 1, v___f_26_);
lean_ctor_set(v___x_24_, 0, v___x_30_);
v___x_35_ = v___x_24_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_30_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___f_26_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v___f_33_);
lean_ctor_set(v_reuseFailAlloc_61_, 3, v___f_32_);
lean_ctor_set(v_reuseFailAlloc_61_, 4, v___f_31_);
v___x_35_ = v_reuseFailAlloc_61_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_37_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 1, v___f_27_);
lean_ctor_set(v___x_17_, 0, v___x_35_);
v___x_37_ = v___x_17_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___f_27_);
v___x_37_ = v_reuseFailAlloc_60_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_38_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_39_ = l_Lean_Core_instMonadRefCoreM;
v___x_40_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_37_);
v___x_41_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_40_, v___x_37_);
v___x_42_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_42_, 0, v___x_38_);
lean_ctor_set(v___x_42_, 1, v___x_39_);
lean_ctor_set(v___x_42_, 2, v___x_41_);
v___x_43_ = l_Lean_Syntax_isLit_x3f(v_k_8_, v_x_9_);
if (lean_obj_tag(v___x_43_) == 1)
{
lean_object* v_val_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_51_; 
lean_dec_ref(v___x_42_);
lean_dec_ref(v___x_37_);
lean_dec(v_x_9_);
v_val_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_51_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_val_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 0);
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_val_44_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_231__overap_58_; lean_object* v___x_59_; 
lean_dec(v___x_43_);
v___x_52_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4));
v___x_53_ = lean_string_append(v___x_52_, v_name_10_);
v___x_54_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5));
v___x_55_ = lean_string_append(v___x_53_, v___x_54_);
v___x_56_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
v___x_57_ = l_Lean_MessageData_ofFormat(v___x_56_);
v___x_231__overap_58_ = l_Lean_throwErrorAt___redArg(v___x_37_, v___x_42_, v_x_9_, v___x_57_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
v___x_59_ = lean_apply_3(v___x_231__overap_58_, v_a_11_, v_a_12_, lean_box(0));
return v___x_59_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(lean_object* v_k_66_, lean_object* v_x_67_, lean_object* v_name_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(v_k_66_, v_x_67_, v_name_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec_ref(v_name_68_);
lean_dec(v_k_66_);
return v_res_72_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_73_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
lean_ctor_set(v___x_78_, 2, v___x_77_);
lean_ctor_set(v___x_78_, 3, v___x_76_);
lean_ctor_set(v___x_78_, 4, v___x_76_);
lean_ctor_set(v___x_78_, 5, v___x_76_);
lean_ctor_set(v___x_78_, 6, v___x_76_);
lean_ctor_set(v___x_78_, 7, v___x_76_);
lean_ctor_set(v___x_78_, 8, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(32u);
v___x_80_ = lean_mk_empty_array_with_capacity(v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = ((size_t)5ULL);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_unsigned_to_nat(32u);
v___x_85_ = lean_mk_empty_array_with_capacity(v___x_84_);
v___x_86_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3);
v___x_87_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_83_);
lean_ctor_set(v___x_87_, 3, v___x_83_);
lean_ctor_set_usize(v___x_87_, 4, v___x_82_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_box(1);
v___x_89_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4);
v___x_90_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
v___x_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_88_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(lean_object* v_msgData_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_env_97_; lean_object* v_options_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_96_ = lean_st_ref_get(v___y_94_);
v_env_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_env_97_);
lean_dec(v___x_96_);
v_options_98_ = lean_ctor_get(v___y_93_, 2);
v___x_99_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_98_);
v___x_101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_101_, 0, v_env_97_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_100_);
lean_ctor_set(v___x_101_, 3, v_options_98_);
v___x_102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v_msgData_92_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msgData_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_ref_113_; lean_object* v___x_114_; lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_123_; 
v_ref_113_ = lean_ctor_get(v___y_110_, 5);
v___x_114_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_109_, v___y_110_, v___y_111_);
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_123_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_121_; 
lean_inc(v_ref_113_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v_ref_113_);
lean_ctor_set(v___x_119_, 1, v_a_115_);
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 1);
lean_ctor_set(v___x_117_, 0, v___x_119_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object* v_ref_129_, lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_fileName_134_; lean_object* v_fileMap_135_; lean_object* v_options_136_; lean_object* v_currRecDepth_137_; lean_object* v_maxRecDepth_138_; lean_object* v_ref_139_; lean_object* v_currNamespace_140_; lean_object* v_openDecls_141_; lean_object* v_initHeartbeats_142_; lean_object* v_maxHeartbeats_143_; lean_object* v_quotContext_144_; lean_object* v_currMacroScope_145_; uint8_t v_diag_146_; lean_object* v_cancelTk_x3f_147_; uint8_t v_suppressElabErrors_148_; lean_object* v_inheritedTraceOptions_149_; lean_object* v_ref_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_fileName_134_ = lean_ctor_get(v___y_131_, 0);
v_fileMap_135_ = lean_ctor_get(v___y_131_, 1);
v_options_136_ = lean_ctor_get(v___y_131_, 2);
v_currRecDepth_137_ = lean_ctor_get(v___y_131_, 3);
v_maxRecDepth_138_ = lean_ctor_get(v___y_131_, 4);
v_ref_139_ = lean_ctor_get(v___y_131_, 5);
v_currNamespace_140_ = lean_ctor_get(v___y_131_, 6);
v_openDecls_141_ = lean_ctor_get(v___y_131_, 7);
v_initHeartbeats_142_ = lean_ctor_get(v___y_131_, 8);
v_maxHeartbeats_143_ = lean_ctor_get(v___y_131_, 9);
v_quotContext_144_ = lean_ctor_get(v___y_131_, 10);
v_currMacroScope_145_ = lean_ctor_get(v___y_131_, 11);
v_diag_146_ = lean_ctor_get_uint8(v___y_131_, sizeof(void*)*14);
v_cancelTk_x3f_147_ = lean_ctor_get(v___y_131_, 12);
v_suppressElabErrors_148_ = lean_ctor_get_uint8(v___y_131_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_149_ = lean_ctor_get(v___y_131_, 13);
v_ref_150_ = l_Lean_replaceRef(v_ref_129_, v_ref_139_);
lean_inc_ref(v_inheritedTraceOptions_149_);
lean_inc(v_cancelTk_x3f_147_);
lean_inc(v_currMacroScope_145_);
lean_inc(v_quotContext_144_);
lean_inc(v_maxHeartbeats_143_);
lean_inc(v_initHeartbeats_142_);
lean_inc(v_openDecls_141_);
lean_inc(v_currNamespace_140_);
lean_inc(v_maxRecDepth_138_);
lean_inc(v_currRecDepth_137_);
lean_inc_ref(v_options_136_);
lean_inc_ref(v_fileMap_135_);
lean_inc_ref(v_fileName_134_);
v___x_151_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_151_, 0, v_fileName_134_);
lean_ctor_set(v___x_151_, 1, v_fileMap_135_);
lean_ctor_set(v___x_151_, 2, v_options_136_);
lean_ctor_set(v___x_151_, 3, v_currRecDepth_137_);
lean_ctor_set(v___x_151_, 4, v_maxRecDepth_138_);
lean_ctor_set(v___x_151_, 5, v_ref_150_);
lean_ctor_set(v___x_151_, 6, v_currNamespace_140_);
lean_ctor_set(v___x_151_, 7, v_openDecls_141_);
lean_ctor_set(v___x_151_, 8, v_initHeartbeats_142_);
lean_ctor_set(v___x_151_, 9, v_maxHeartbeats_143_);
lean_ctor_set(v___x_151_, 10, v_quotContext_144_);
lean_ctor_set(v___x_151_, 11, v_currMacroScope_145_);
lean_ctor_set(v___x_151_, 12, v_cancelTk_x3f_147_);
lean_ctor_set(v___x_151_, 13, v_inheritedTraceOptions_149_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*14, v_diag_146_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*14 + 1, v_suppressElabErrors_148_);
v___x_152_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_130_, v___x_151_, v___y_132_);
lean_dec_ref(v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object* v_ref_153_, lean_object* v_msg_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_153_, v_msg_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v_ref_153_);
return v_res_158_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4));
v___x_168_ = l_Lean_stringToMessageData(v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object* v_x_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_183_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_179_);
v___x_184_ = l_Lean_Syntax_isOfKind(v_x_179_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_186_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_179_, v___x_185_, v_a_180_, v_a_181_);
lean_dec(v_x_179_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = l_Lean_Syntax_getArg(v_x_179_, v___x_187_);
v___x_189_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7));
lean_inc(v___x_188_);
v___x_190_ = l_Lean_Syntax_isOfKind(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9));
v___x_192_ = l_Lean_Syntax_isOfKind(v___x_188_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_194_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_179_, v___x_193_, v_a_180_, v_a_181_);
lean_dec(v_x_179_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v_x_179_);
v___x_195_ = lean_box(v___x_190_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v___x_188_);
lean_dec(v_x_179_);
v___x_197_ = lean_box(v___x_190_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object* v_x_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_199_, v_a_200_, v_a_201_);
lean_dec(v_a_201_);
lean_dec_ref(v_a_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object* v_00_u03b1_204_, lean_object* v_ref_205_, lean_object* v_msg_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_205_, v_msg_206_, v___y_207_, v___y_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object* v_00_u03b1_211_, lean_object* v_ref_212_, lean_object* v_msg_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(v_00_u03b1_211_, v_ref_212_, v_msg_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v_ref_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object* v_00_u03b1_218_, lean_object* v_msg_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_219_, v___y_220_, v___y_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object* v_00_u03b1_224_, lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(v_00_u03b1_224_, v_msg_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object* v___x_230_, lean_object* v_s_231_, lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v_startInclusive_234_; lean_object* v_endExclusive_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_startInclusive_234_ = lean_ctor_get(v___x_230_, 1);
v_endExclusive_235_ = lean_ctor_get(v___x_230_, 2);
v___x_236_ = lean_nat_sub(v_endExclusive_235_, v_startInclusive_234_);
v___x_237_ = lean_nat_dec_eq(v_a_232_, v___x_236_);
lean_dec(v___x_236_);
if (v___x_237_ == 0)
{
uint32_t v___x_238_; lean_object* v___x_239_; uint32_t v___x_240_; uint8_t v___x_241_; 
v___x_238_ = lean_string_utf8_get_fast(v_s_231_, v_a_232_);
v___x_239_ = lean_string_utf8_next_fast(v_s_231_, v_a_232_);
lean_dec(v_a_232_);
v___x_240_ = 95;
v___x_241_ = lean_uint32_dec_eq(v___x_238_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; uint32_t v___x_244_; uint32_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_242_ = lean_unsigned_to_nat(10u);
v___x_243_ = lean_nat_mul(v_b_233_, v___x_242_);
lean_dec(v_b_233_);
v___x_244_ = 48;
v___x_245_ = lean_uint32_sub(v___x_238_, v___x_244_);
v___x_246_ = lean_uint32_to_nat(v___x_245_);
v___x_247_ = lean_nat_add(v___x_243_, v___x_246_);
lean_dec(v___x_246_);
lean_dec(v___x_243_);
v_a_232_ = v___x_239_;
v_b_233_ = v___x_247_;
goto _start;
}
else
{
v_a_232_ = v___x_239_;
goto _start;
}
}
else
{
lean_dec(v_a_232_);
return v_b_233_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object* v___x_250_, lean_object* v_s_251_, lean_object* v_a_252_, lean_object* v_b_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_250_, v_s_251_, v_a_252_, v_b_253_);
lean_dec_ref(v_s_251_);
lean_dec_ref(v___x_250_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object* v_s_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_string_utf8_byte_size(v_s_255_);
lean_inc_ref(v_s_255_);
v___x_258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_258_, 0, v_s_255_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
lean_ctor_set(v___x_258_, 2, v___x_257_);
v___x_259_ = l_String_Slice_positions(v___x_258_);
v___x_260_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_258_, v_s_255_, v___x_259_, v___x_256_);
lean_dec_ref(v_s_255_);
lean_dec_ref(v___x_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object* v___x_261_, lean_object* v_s_262_, lean_object* v_inst_263_, lean_object* v_R_264_, lean_object* v_a_265_, lean_object* v_b_266_, lean_object* v_c_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_261_, v_s_262_, v_a_265_, v_b_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object* v___x_269_, lean_object* v_s_270_, lean_object* v_inst_271_, lean_object* v_R_272_, lean_object* v_a_273_, lean_object* v_b_274_, lean_object* v_c_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(v___x_269_, v_s_270_, v_inst_271_, v_R_272_, v_a_273_, v_b_274_, v_c_275_);
lean_dec_ref(v_s_270_);
lean_dec_ref(v___x_269_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object* v_s_277_){
_start:
{
uint32_t v___y_279_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_string_utf8_byte_size(v_s_277_);
lean_inc_ref(v_s_277_);
v___x_304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_304_, 0, v_s_277_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_303_);
v___x_305_ = l_String_Slice_Pos_get_x3f(v___x_304_, v___x_302_);
lean_dec_ref(v___x_304_);
if (lean_obj_tag(v___x_305_) == 0)
{
uint32_t v___x_306_; 
v___x_306_ = 65;
v___y_279_ = v___x_306_;
goto v___jp_278_;
}
else
{
lean_object* v_val_307_; uint32_t v___x_308_; 
v_val_307_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_val_307_);
lean_dec_ref(v___x_305_);
v___x_308_ = lean_unbox_uint32(v_val_307_);
lean_dec(v_val_307_);
v___y_279_ = v___x_308_;
goto v___jp_278_;
}
v___jp_278_:
{
uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = 45;
v___x_281_ = lean_uint32_dec_eq(v___y_279_, v___x_280_);
if (v___x_281_ == 0)
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 43;
v___x_283_ = lean_uint32_dec_eq(v___y_279_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_box(v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v_s_277_);
return v___x_285_;
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_string_utf8_byte_size(v_s_277_);
lean_inc_ref(v_s_277_);
v___x_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_289_, 0, v_s_277_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
lean_ctor_set(v___x_289_, 2, v___x_288_);
v___x_290_ = l_String_Slice_Pos_nextn(v___x_289_, v___x_287_, v___x_286_);
lean_dec_ref(v___x_289_);
v___x_291_ = lean_string_utf8_extract(v_s_277_, v___x_290_, v___x_288_);
lean_dec(v___x_290_);
lean_dec_ref(v_s_277_);
v___x_292_ = lean_box(v___x_281_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_291_);
return v___x_293_;
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_294_ = lean_unsigned_to_nat(1u);
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_string_utf8_byte_size(v_s_277_);
lean_inc_ref(v_s_277_);
v___x_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_297_, 0, v_s_277_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
lean_ctor_set(v___x_297_, 2, v___x_296_);
v___x_298_ = l_String_Slice_Pos_nextn(v___x_297_, v___x_295_, v___x_294_);
lean_dec_ref(v___x_297_);
v___x_299_ = lean_string_utf8_extract(v_s_277_, v___x_298_, v___x_296_);
lean_dec(v___x_298_);
lean_dec_ref(v_s_277_);
v___x_300_ = lean_box(v___x_281_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object* v_s_309_){
_start:
{
uint8_t v_fst_311_; lean_object* v_snd_312_; uint32_t v___y_318_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_string_utf8_byte_size(v_s_309_);
lean_inc_ref(v_s_309_);
v___x_337_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_337_, 0, v_s_309_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
v___x_338_ = l_String_Slice_Pos_get_x3f(v___x_337_, v___x_335_);
lean_dec_ref(v___x_337_);
if (lean_obj_tag(v___x_338_) == 0)
{
uint32_t v___x_339_; 
v___x_339_ = 65;
v___y_318_ = v___x_339_;
goto v___jp_317_;
}
else
{
lean_object* v_val_340_; uint32_t v___x_341_; 
v_val_340_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_340_);
lean_dec_ref(v___x_338_);
v___x_341_ = lean_unbox_uint32(v_val_340_);
lean_dec(v_val_340_);
v___y_318_ = v___x_341_;
goto v___jp_317_;
}
v___jp_310_:
{
if (v_fst_311_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_312_);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_312_);
v___x_316_ = l_Int_negOfNat(v___x_315_);
lean_dec(v___x_315_);
return v___x_316_;
}
}
v___jp_317_:
{
uint32_t v___x_319_; uint8_t v___x_320_; 
v___x_319_ = 45;
v___x_320_ = lean_uint32_dec_eq(v___y_318_, v___x_319_);
if (v___x_320_ == 0)
{
uint32_t v___x_321_; uint8_t v___x_322_; 
v___x_321_ = 43;
v___x_322_ = lean_uint32_dec_eq(v___y_318_, v___x_321_);
if (v___x_322_ == 0)
{
v_fst_311_ = v___x_322_;
v_snd_312_ = v_s_309_;
goto v___jp_310_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_string_utf8_byte_size(v_s_309_);
lean_inc_ref(v_s_309_);
v___x_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_326_, 0, v_s_309_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
lean_ctor_set(v___x_326_, 2, v___x_325_);
v___x_327_ = l_String_Slice_Pos_nextn(v___x_326_, v___x_324_, v___x_323_);
lean_dec_ref(v___x_326_);
v___x_328_ = lean_string_utf8_extract(v_s_309_, v___x_327_, v___x_325_);
lean_dec(v___x_327_);
lean_dec_ref(v_s_309_);
v_fst_311_ = v___x_320_;
v_snd_312_ = v___x_328_;
goto v___jp_310_;
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_string_utf8_byte_size(v_s_309_);
lean_inc_ref(v_s_309_);
v___x_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_332_, 0, v_s_309_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_331_);
v___x_333_ = l_String_Slice_Pos_nextn(v___x_332_, v___x_330_, v___x_329_);
lean_dec_ref(v___x_332_);
v___x_334_ = lean_string_utf8_extract(v_s_309_, v___x_333_, v___x_331_);
lean_dec(v___x_333_);
lean_dec_ref(v_s_309_);
v_fst_311_ = v___x_320_;
v_snd_312_ = v___x_334_;
goto v___jp_310_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3));
v___x_351_ = l_Lean_MessageData_ofFormat(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object* v_x_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_a_357_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
v___x_361_ = l_Lean_Syntax_isLit_x3f(v___x_360_, v_x_352_);
if (lean_obj_tag(v___x_361_) == 1)
{
lean_object* v_val_362_; 
v_val_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_val_362_);
lean_dec_ref(v___x_361_);
v_a_357_ = v_val_362_;
goto v___jp_356_;
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec(v___x_361_);
v___x_363_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4);
v___x_364_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_352_, v___x_363_, v_a_353_, v_a_354_);
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_a_357_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object* v_x_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_x_373_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object* v___x_378_, lean_object* v_s_379_, lean_object* v_a_380_, lean_object* v_b_381_){
_start:
{
lean_object* v_startInclusive_382_; lean_object* v_endExclusive_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_startInclusive_382_ = lean_ctor_get(v___x_378_, 1);
v_endExclusive_383_ = lean_ctor_get(v___x_378_, 2);
v___x_384_ = lean_nat_sub(v_endExclusive_383_, v_startInclusive_382_);
v___x_385_ = lean_nat_dec_eq(v_a_380_, v___x_384_);
lean_dec(v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v_fst_386_; lean_object* v_snd_387_; uint32_t v___x_388_; lean_object* v___x_389_; uint32_t v___x_390_; uint8_t v___x_391_; 
v_fst_386_ = lean_ctor_get(v_b_381_, 0);
v_snd_387_ = lean_ctor_get(v_b_381_, 1);
v___x_388_ = lean_string_utf8_get_fast(v_s_379_, v_a_380_);
v___x_389_ = lean_string_utf8_next_fast(v_s_379_, v_a_380_);
lean_dec(v_a_380_);
v___x_390_ = 95;
v___x_391_ = lean_uint32_dec_eq(v___x_388_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_414_; 
lean_inc(v_snd_387_);
lean_inc(v_fst_386_);
v_isSharedCheck_414_ = !lean_is_exclusive(v_b_381_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; lean_object* v_unused_416_; 
v_unused_415_ = lean_ctor_get(v_b_381_, 1);
lean_dec(v_unused_415_);
v_unused_416_ = lean_ctor_get(v_b_381_, 0);
lean_dec(v_unused_416_);
v___x_393_ = v_b_381_;
v_isShared_394_ = v_isSharedCheck_414_;
goto v_resetjp_392_;
}
else
{
lean_dec(v_b_381_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_414_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
uint32_t v___x_395_; uint8_t v___x_396_; 
v___x_395_ = 46;
v___x_396_ = lean_uint32_dec_eq(v___x_388_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; uint32_t v___x_399_; uint32_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_397_ = lean_unsigned_to_nat(10u);
v___x_398_ = lean_nat_mul(v_fst_386_, v___x_397_);
lean_dec(v_fst_386_);
v___x_399_ = 48;
v___x_400_ = lean_uint32_sub(v___x_388_, v___x_399_);
v___x_401_ = lean_uint32_to_nat(v___x_400_);
v___x_402_ = lean_nat_add(v___x_398_, v___x_401_);
lean_dec(v___x_401_);
lean_dec(v___x_398_);
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_snd_387_, v___x_403_);
lean_dec(v_snd_387_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v___x_404_);
lean_ctor_set(v___x_393_, 0, v___x_402_);
v___x_406_ = v___x_393_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_404_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
v_a_380_ = v___x_389_;
v_b_381_ = v___x_406_;
goto _start;
}
}
else
{
lean_object* v___x_409_; lean_object* v___x_411_; 
lean_dec(v_snd_387_);
v___x_409_ = lean_unsigned_to_nat(0u);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v___x_409_);
v___x_411_ = v___x_393_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_fst_386_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_409_);
v___x_411_ = v_reuseFailAlloc_413_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
v_a_380_ = v___x_389_;
v_b_381_ = v___x_411_;
goto _start;
}
}
}
}
else
{
v_a_380_ = v___x_389_;
goto _start;
}
}
else
{
lean_dec(v_a_380_);
return v_b_381_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object* v___x_418_, lean_object* v_s_419_, lean_object* v_a_420_, lean_object* v_b_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_418_, v_s_419_, v_a_420_, v_b_421_);
lean_dec_ref(v_s_419_);
lean_dec_ref(v___x_418_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object* v_s_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_fst_431_; lean_object* v_snd_432_; uint8_t v___x_433_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_string_length(v_s_423_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_string_utf8_byte_size(v_s_423_);
lean_inc_ref(v_s_423_);
v___x_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_428_, 0, v_s_423_);
lean_ctor_set(v___x_428_, 1, v___x_424_);
lean_ctor_set(v___x_428_, 2, v___x_427_);
v___x_429_ = l_String_Slice_positions(v___x_428_);
v___x_430_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_428_, v_s_423_, v___x_429_, v___x_426_);
lean_dec_ref(v_s_423_);
lean_dec_ref(v___x_428_);
v_fst_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_fst_431_);
v_snd_432_ = lean_ctor_get(v___x_430_, 1);
lean_inc(v_snd_432_);
v___x_433_ = lean_nat_dec_le(v___x_425_, v_snd_432_);
lean_dec(v_snd_432_);
if (v___x_433_ == 0)
{
lean_dec(v_fst_431_);
return v___x_430_;
}
else
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_440_; 
v_isSharedCheck_440_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; lean_object* v_unused_442_; 
v_unused_441_ = lean_ctor_get(v___x_430_, 1);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v___x_430_, 0);
lean_dec(v_unused_442_);
v___x_435_ = v___x_430_;
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
else
{
lean_dec(v___x_430_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_440_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_438_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_424_);
v___x_438_ = v___x_435_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_fst_431_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v___x_424_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object* v___x_443_, lean_object* v_s_444_, lean_object* v_inst_445_, lean_object* v_R_446_, lean_object* v_a_447_, lean_object* v_b_448_, lean_object* v_c_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_443_, v_s_444_, v_a_447_, v_b_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object* v___x_451_, lean_object* v_s_452_, lean_object* v_inst_453_, lean_object* v_R_454_, lean_object* v_a_455_, lean_object* v_b_456_, lean_object* v_c_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(v___x_451_, v_s_452_, v_inst_453_, v_R_454_, v_a_455_, v_b_456_, v_c_457_);
lean_dec_ref(v_s_452_);
lean_dec_ref(v___x_451_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object* v_s_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0));
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object* v_s_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v_s_463_);
lean_dec_ref(v_s_463_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object* v_s_465_, lean_object* v___x_466_, lean_object* v___x_467_, lean_object* v_a_468_, lean_object* v_b_469_){
_start:
{
lean_object* v_it_471_; lean_object* v_startInclusive_472_; lean_object* v_endExclusive_473_; 
if (lean_obj_tag(v_a_468_) == 0)
{
lean_object* v_currPos_478_; lean_object* v_searcher_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_509_; 
v_currPos_478_ = lean_ctor_get(v_a_468_, 0);
v_searcher_479_ = lean_ctor_get(v_a_468_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_509_ == 0)
{
v___x_481_ = v_a_468_;
v_isShared_482_ = v_isSharedCheck_509_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_searcher_479_);
lean_inc(v_currPos_478_);
lean_dec(v_a_468_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_509_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
uint8_t v___y_484_; lean_object* v_startInclusive_499_; lean_object* v_endExclusive_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_startInclusive_499_ = lean_ctor_get(v___x_466_, 1);
v_endExclusive_500_ = lean_ctor_get(v___x_466_, 2);
v___x_501_ = lean_nat_sub(v_endExclusive_500_, v_startInclusive_499_);
v___x_502_ = lean_nat_dec_eq(v_searcher_479_, v___x_501_);
lean_dec(v___x_501_);
if (v___x_502_ == 0)
{
uint32_t v___x_503_; uint32_t v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_string_utf8_get_fast(v_s_465_, v_searcher_479_);
v___x_504_ = 69;
v___x_505_ = lean_uint32_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
uint32_t v___x_506_; uint8_t v___x_507_; 
v___x_506_ = 101;
v___x_507_ = lean_uint32_dec_eq(v___x_503_, v___x_506_);
v___y_484_ = v___x_507_;
goto v___jp_483_;
}
else
{
v___y_484_ = v___x_505_;
goto v___jp_483_;
}
}
else
{
lean_object* v___x_508_; 
lean_del_object(v___x_481_);
lean_dec(v_searcher_479_);
v___x_508_ = lean_box(1);
lean_inc(v___x_467_);
v_it_471_ = v___x_508_;
v_startInclusive_472_ = v_currPos_478_;
v_endExclusive_473_ = v___x_467_;
goto v___jp_470_;
}
v___jp_483_:
{
if (v___y_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = lean_string_utf8_next_fast(v_s_465_, v_searcher_479_);
lean_dec(v_searcher_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_485_);
v___x_487_ = v___x_481_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_currPos_478_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_485_);
v___x_487_ = v_reuseFailAlloc_489_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v_a_468_ = v___x_487_;
goto _start;
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v_slice_493_; lean_object* v_nextIt_495_; 
v___x_490_ = lean_string_utf8_next_fast(v_s_465_, v_searcher_479_);
v___x_491_ = lean_nat_sub(v___x_490_, v_searcher_479_);
v___x_492_ = lean_nat_add(v_searcher_479_, v___x_491_);
lean_dec(v___x_491_);
v_slice_493_ = l_String_Slice_subslice_x21(v___x_466_, v_currPos_478_, v_searcher_479_);
lean_inc(v___x_492_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_492_);
lean_ctor_set(v___x_481_, 0, v___x_492_);
v_nextIt_495_ = v___x_481_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_492_);
v_nextIt_495_ = v_reuseFailAlloc_498_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v_startInclusive_496_; lean_object* v_endExclusive_497_; 
v_startInclusive_496_ = lean_ctor_get(v_slice_493_, 0);
lean_inc(v_startInclusive_496_);
v_endExclusive_497_ = lean_ctor_get(v_slice_493_, 1);
lean_inc(v_endExclusive_497_);
lean_dec_ref(v_slice_493_);
v_it_471_ = v_nextIt_495_;
v_startInclusive_472_ = v_startInclusive_496_;
v_endExclusive_473_ = v_endExclusive_497_;
goto v___jp_470_;
}
}
}
}
}
else
{
lean_dec(v___x_467_);
lean_dec_ref(v_s_465_);
return v_b_469_;
}
v___jp_470_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_inc_ref(v_s_465_);
v___x_474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_474_, 0, v_s_465_);
lean_ctor_set(v___x_474_, 1, v_startInclusive_472_);
lean_ctor_set(v___x_474_, 2, v_endExclusive_473_);
v___x_475_ = l_String_Slice_toString(v___x_474_);
lean_dec_ref(v___x_474_);
v___x_476_ = lean_array_push(v_b_469_, v___x_475_);
v_a_468_ = v_it_471_;
v_b_469_ = v___x_476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object* v_s_510_, lean_object* v___x_511_, lean_object* v___x_512_, lean_object* v_a_513_, lean_object* v_b_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_510_, v___x_511_, v___x_512_, v_a_513_, v_b_514_);
lean_dec_ref(v___x_511_);
return v_res_515_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_nat_to_int(v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object* v_s_523_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_string_utf8_byte_size(v_s_523_);
lean_inc_ref(v_s_523_);
v___x_528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_528_, 0, v_s_523_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
lean_ctor_set(v___x_528_, 2, v___x_527_);
v___x_529_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v___x_528_);
v___x_530_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2));
v___x_531_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_523_, v___x_528_, v___x_527_, v___x_529_, v___x_530_);
lean_dec_ref(v___x_528_);
v___x_532_ = lean_array_to_list(v___x_531_);
if (lean_obj_tag(v___x_532_) == 1)
{
lean_object* v_tail_533_; 
v_tail_533_ = lean_ctor_get(v___x_532_, 1);
lean_inc(v_tail_533_);
if (lean_obj_tag(v_tail_533_) == 0)
{
lean_object* v_head_534_; lean_object* v___x_535_; lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_545_; 
v_head_534_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_head_534_);
lean_dec_ref(v___x_532_);
v___x_535_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_534_);
v_fst_536_ = lean_ctor_get(v___x_535_, 0);
v_snd_537_ = lean_ctor_get(v___x_535_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_545_ == 0)
{
v___x_539_ = v___x_535_;
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snd_537_);
lean_inc(v_fst_536_);
lean_dec(v___x_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_545_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = l_Int_negOfNat(v_snd_537_);
lean_dec(v_snd_537_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_fst_536_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
lean_object* v_tail_546_; 
v_tail_546_ = lean_ctor_get(v_tail_533_, 1);
if (lean_obj_tag(v_tail_546_) == 0)
{
lean_object* v_head_547_; lean_object* v_head_548_; lean_object* v___x_549_; lean_object* v_fst_550_; lean_object* v_snd_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_561_; 
v_head_547_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_head_547_);
lean_dec_ref(v___x_532_);
v_head_548_ = lean_ctor_get(v_tail_533_, 0);
lean_inc(v_head_548_);
lean_dec_ref(v_tail_533_);
v___x_549_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_547_);
v_fst_550_ = lean_ctor_get(v___x_549_, 0);
v_snd_551_ = lean_ctor_get(v___x_549_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_561_ == 0)
{
v___x_553_ = v___x_549_;
v_isShared_554_ = v_isSharedCheck_561_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_snd_551_);
lean_inc(v_fst_550_);
lean_dec(v___x_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_561_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_exp_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
v_exp_555_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_head_548_);
v___x_556_ = l_Int_negOfNat(v_snd_551_);
lean_dec(v_snd_551_);
v___x_557_ = lean_int_add(v___x_556_, v_exp_555_);
lean_dec(v_exp_555_);
lean_dec(v___x_556_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___x_557_);
v___x_559_ = v___x_553_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_fst_550_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
else
{
lean_dec_ref(v_tail_533_);
lean_dec_ref(v___x_532_);
goto v___jp_524_;
}
}
}
else
{
lean_dec(v___x_532_);
goto v___jp_524_;
}
v___jp_524_:
{
lean_object* v___x_525_; 
v___x_525_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1);
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object* v_s_562_, lean_object* v___x_563_, lean_object* v___x_564_, lean_object* v_inst_565_, lean_object* v_R_566_, lean_object* v_a_567_, lean_object* v_b_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_562_, v___x_563_, v___x_564_, v_a_567_, v_b_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object* v_s_570_, lean_object* v___x_571_, lean_object* v___x_572_, lean_object* v_inst_573_, lean_object* v_R_574_, lean_object* v_a_575_, lean_object* v_b_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(v_s_570_, v___x_571_, v___x_572_, v_inst_573_, v_R_574_, v_a_575_, v_b_576_);
lean_dec_ref(v___x_571_);
return v_res_577_;
}
}
static double _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2(void){
_start:
{
lean_object* v___x_580_; double v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_float_of_nat(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object* v_s_582_){
_start:
{
lean_object* v___x_583_; lean_object* v_fst_584_; lean_object* v_snd_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_583_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(v_s_582_);
v_fst_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_fst_584_);
v_snd_585_ = lean_ctor_get(v___x_583_, 1);
lean_inc(v_snd_585_);
lean_dec_ref(v___x_583_);
v___x_586_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0));
v___x_587_ = lean_string_dec_eq(v_snd_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1));
v___x_589_ = lean_string_dec_eq(v_snd_585_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; double v_flt_596_; uint8_t v___x_597_; 
v___x_590_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(v_snd_585_);
v_fst_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_fst_591_);
v_snd_592_ = lean_ctor_get(v___x_590_, 1);
lean_inc(v_snd_592_);
lean_dec_ref(v___x_590_);
v___x_593_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_594_ = lean_int_dec_lt(v_snd_592_, v___x_593_);
v___x_595_ = lean_nat_abs(v_snd_592_);
lean_dec(v_snd_592_);
v_flt_596_ = l_Float_ofScientific(v_fst_591_, v___x_594_, v___x_595_);
lean_dec(v_fst_591_);
v___x_597_ = lean_unbox(v_fst_584_);
lean_dec(v_fst_584_);
if (v___x_597_ == 0)
{
return v_flt_596_;
}
else
{
double v___x_598_; 
v___x_598_ = lean_float_negate(v_flt_596_);
return v___x_598_;
}
}
else
{
uint8_t v___x_599_; 
lean_dec(v_snd_585_);
v___x_599_ = lean_unbox(v_fst_584_);
lean_dec(v_fst_584_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; double v___x_602_; double v___x_603_; double v___x_604_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_unsigned_to_nat(1u);
v___x_602_ = l_Float_ofScientific(v___x_600_, v___x_589_, v___x_601_);
v___x_603_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_604_ = lean_float_div(v___x_602_, v___x_603_);
return v___x_604_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; double v___x_607_; double v___x_608_; double v___x_609_; double v___x_610_; 
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = l_Float_ofScientific(v___x_605_, v___x_589_, v___x_606_);
v___x_608_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_609_ = lean_float_div(v___x_607_, v___x_608_);
v___x_610_ = lean_float_negate(v___x_609_);
return v___x_610_;
}
}
}
else
{
uint8_t v___x_611_; 
lean_dec(v_snd_585_);
v___x_611_ = lean_unbox(v_fst_584_);
lean_dec(v_fst_584_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; double v___x_614_; double v___x_615_; double v___x_616_; 
v___x_612_ = lean_unsigned_to_nat(10u);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = l_Float_ofScientific(v___x_612_, v___x_587_, v___x_613_);
v___x_615_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_616_ = lean_float_div(v___x_614_, v___x_615_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; double v___x_619_; double v___x_620_; double v___x_621_; double v___x_622_; 
v___x_617_ = lean_unsigned_to_nat(10u);
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = l_Float_ofScientific(v___x_617_, v___x_587_, v___x_618_);
v___x_620_ = lean_float_negate(v___x_619_);
v___x_621_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_622_ = lean_float_div(v___x_620_, v___x_621_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object* v_s_623_){
_start:
{
double v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_s_623_);
v_r_625_ = lean_box_float(v_res_624_);
return v_r_625_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3));
v___x_635_ = l_Lean_MessageData_ofFormat(v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object* v_x_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_a_641_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
v___x_646_ = l_Lean_Syntax_isLit_x3f(v___x_645_, v_x_636_);
if (lean_obj_tag(v___x_646_) == 1)
{
lean_object* v_val_647_; 
v_val_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_647_);
lean_dec_ref(v___x_646_);
v_a_641_ = v_val_647_;
goto v___jp_640_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v___x_646_);
v___x_648_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4);
v___x_649_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_636_, v___x_648_, v_a_637_, v_a_638_);
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
v___jp_640_:
{
double v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_a_641_);
v___x_643_ = lean_box_float(v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object* v_x_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_658_, v_a_659_, v_a_660_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_x_658_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_b_667_){
_start:
{
lean_object* v_startInclusive_668_; lean_object* v_endExclusive_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_startInclusive_668_ = lean_ctor_get(v___x_663_, 1);
v_endExclusive_669_ = lean_ctor_get(v___x_663_, 2);
v___x_670_ = lean_nat_sub(v_endExclusive_669_, v_startInclusive_668_);
v___x_671_ = lean_nat_dec_eq(v_a_666_, v___x_670_);
lean_dec(v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint32_t v___x_675_; uint32_t v___x_676_; uint8_t v___x_677_; 
v___x_672_ = lean_nat_add(v___x_664_, v_a_666_);
lean_dec(v_a_666_);
v___x_673_ = lean_string_utf8_next_fast(v_a_665_, v___x_672_);
v___x_674_ = lean_nat_sub(v___x_673_, v___x_664_);
v___x_675_ = lean_string_utf8_get_fast(v_a_665_, v___x_672_);
lean_dec(v___x_672_);
v___x_676_ = 95;
v___x_677_ = lean_uint32_dec_eq(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; uint32_t v___x_680_; uint32_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_678_ = lean_unsigned_to_nat(2u);
v___x_679_ = lean_nat_mul(v_b_667_, v___x_678_);
lean_dec(v_b_667_);
v___x_680_ = 48;
v___x_681_ = lean_uint32_sub(v___x_675_, v___x_680_);
v___x_682_ = lean_uint32_to_nat(v___x_681_);
v___x_683_ = lean_nat_add(v___x_679_, v___x_682_);
lean_dec(v___x_682_);
lean_dec(v___x_679_);
v_a_666_ = v___x_674_;
v_b_667_ = v___x_683_;
goto _start;
}
else
{
v_a_666_ = v___x_674_;
goto _start;
}
}
else
{
lean_dec(v_a_666_);
return v_b_667_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object* v___x_686_, lean_object* v___x_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_b_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_686_, v___x_687_, v_a_688_, v_a_689_, v_b_690_);
lean_dec_ref(v_a_688_);
lean_dec(v___x_687_);
lean_dec_ref(v___x_686_);
return v_res_691_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3));
v___x_701_ = l_Lean_MessageData_ofFormat(v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object* v_x_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_a_707_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
v___x_718_ = l_Lean_Syntax_isLit_x3f(v___x_717_, v_x_702_);
if (lean_obj_tag(v___x_718_) == 1)
{
lean_object* v_val_719_; 
v_val_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_val_719_);
lean_dec_ref(v___x_718_);
v_a_707_ = v_val_719_;
goto v___jp_706_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v___x_718_);
v___x_720_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4);
v___x_721_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_702_, v___x_720_, v_a_703_, v_a_704_);
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = lean_unsigned_to_nat(2u);
v___x_710_ = lean_string_utf8_byte_size(v_a_707_);
lean_inc_ref(v_a_707_);
v___x_711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_711_, 0, v_a_707_);
lean_ctor_set(v___x_711_, 1, v___x_708_);
lean_ctor_set(v___x_711_, 2, v___x_710_);
v___x_712_ = l_String_Slice_Pos_nextn(v___x_711_, v___x_708_, v___x_709_);
lean_dec_ref(v___x_711_);
lean_inc(v___x_712_);
lean_inc_ref(v_a_707_);
v___x_713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_713_, 0, v_a_707_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
lean_ctor_set(v___x_713_, 2, v___x_710_);
v___x_714_ = l_String_Slice_positions(v___x_713_);
v___x_715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_713_, v___x_712_, v_a_707_, v___x_714_, v___x_708_);
lean_dec_ref(v_a_707_);
lean_dec(v___x_712_);
lean_dec_ref(v___x_713_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object* v_x_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_730_, v_a_731_, v_a_732_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_x_730_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object* v___x_735_, lean_object* v___x_736_, lean_object* v_a_737_, lean_object* v_inst_738_, lean_object* v_R_739_, lean_object* v_a_740_, lean_object* v_b_741_, lean_object* v_c_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_735_, v___x_736_, v_a_737_, v_a_740_, v_b_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object* v___x_744_, lean_object* v___x_745_, lean_object* v_a_746_, lean_object* v_inst_747_, lean_object* v_R_748_, lean_object* v_a_749_, lean_object* v_b_750_, lean_object* v_c_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(v___x_744_, v___x_745_, v_a_746_, v_inst_747_, v_R_748_, v_a_749_, v_b_750_, v_c_751_);
lean_dec_ref(v_a_746_);
lean_dec(v___x_745_);
lean_dec_ref(v___x_744_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object* v___x_753_, lean_object* v___x_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_b_757_){
_start:
{
lean_object* v_startInclusive_758_; lean_object* v_endExclusive_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_startInclusive_758_ = lean_ctor_get(v___x_753_, 1);
v_endExclusive_759_ = lean_ctor_get(v___x_753_, 2);
v___x_760_ = lean_nat_sub(v_endExclusive_759_, v_startInclusive_758_);
v___x_761_ = lean_nat_dec_eq(v_a_756_, v___x_760_);
lean_dec(v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint32_t v___x_765_; uint32_t v___x_766_; uint8_t v___x_767_; 
v___x_762_ = lean_nat_add(v___x_754_, v_a_756_);
lean_dec(v_a_756_);
v___x_763_ = lean_string_utf8_next_fast(v_a_755_, v___x_762_);
v___x_764_ = lean_nat_sub(v___x_763_, v___x_754_);
v___x_765_ = lean_string_utf8_get_fast(v_a_755_, v___x_762_);
lean_dec(v___x_762_);
v___x_766_ = 95;
v___x_767_ = lean_uint32_dec_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; uint32_t v___x_770_; uint32_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_768_ = lean_unsigned_to_nat(8u);
v___x_769_ = lean_nat_mul(v_b_757_, v___x_768_);
lean_dec(v_b_757_);
v___x_770_ = 48;
v___x_771_ = lean_uint32_sub(v___x_765_, v___x_770_);
v___x_772_ = lean_uint32_to_nat(v___x_771_);
v___x_773_ = lean_nat_add(v___x_769_, v___x_772_);
lean_dec(v___x_772_);
lean_dec(v___x_769_);
v_a_756_ = v___x_764_;
v_b_757_ = v___x_773_;
goto _start;
}
else
{
v_a_756_ = v___x_764_;
goto _start;
}
}
else
{
lean_dec(v_a_756_);
return v_b_757_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object* v___x_776_, lean_object* v___x_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_b_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_776_, v___x_777_, v_a_778_, v_a_779_, v_b_780_);
lean_dec_ref(v_a_778_);
lean_dec(v___x_777_);
lean_dec_ref(v___x_776_);
return v_res_781_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3));
v___x_791_ = l_Lean_MessageData_ofFormat(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object* v_x_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_a_797_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
v___x_808_ = l_Lean_Syntax_isLit_x3f(v___x_807_, v_x_792_);
if (lean_obj_tag(v___x_808_) == 1)
{
lean_object* v_val_809_; 
v_val_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_val_809_);
lean_dec_ref(v___x_808_);
v_a_797_ = v_val_809_;
goto v___jp_796_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___x_808_);
v___x_810_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4);
v___x_811_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_792_, v___x_810_, v_a_793_, v_a_794_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
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
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
v___jp_796_:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_unsigned_to_nat(2u);
v___x_800_ = lean_string_utf8_byte_size(v_a_797_);
lean_inc_ref(v_a_797_);
v___x_801_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_801_, 0, v_a_797_);
lean_ctor_set(v___x_801_, 1, v___x_798_);
lean_ctor_set(v___x_801_, 2, v___x_800_);
v___x_802_ = l_String_Slice_Pos_nextn(v___x_801_, v___x_798_, v___x_799_);
lean_dec_ref(v___x_801_);
lean_inc(v___x_802_);
lean_inc_ref(v_a_797_);
v___x_803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_803_, 0, v_a_797_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
lean_ctor_set(v___x_803_, 2, v___x_800_);
v___x_804_ = l_String_Slice_positions(v___x_803_);
v___x_805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_803_, v___x_802_, v_a_797_, v___x_804_, v___x_798_);
lean_dec_ref(v_a_797_);
lean_dec(v___x_802_);
lean_dec_ref(v___x_803_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object* v_x_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_820_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_x_820_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object* v___x_825_, lean_object* v___x_826_, lean_object* v_a_827_, lean_object* v_inst_828_, lean_object* v_R_829_, lean_object* v_a_830_, lean_object* v_b_831_, lean_object* v_c_832_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_825_, v___x_826_, v_a_827_, v_a_830_, v_b_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object* v___x_834_, lean_object* v___x_835_, lean_object* v_a_836_, lean_object* v_inst_837_, lean_object* v_R_838_, lean_object* v_a_839_, lean_object* v_b_840_, lean_object* v_c_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(v___x_834_, v___x_835_, v_a_836_, v_inst_837_, v_R_838_, v_a_839_, v_b_840_, v_c_841_);
lean_dec_ref(v_a_836_);
lean_dec(v___x_835_);
lean_dec_ref(v___x_834_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t v_c_843_){
_start:
{
uint32_t v___x_844_; uint8_t v___x_845_; 
v___x_844_ = 57;
v___x_845_ = lean_uint32_dec_le(v_c_843_, v___x_844_);
if (v___x_845_ == 0)
{
uint32_t v___x_846_; uint8_t v___x_847_; 
v___x_846_ = 70;
v___x_847_ = lean_uint32_dec_le(v_c_843_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; uint32_t v___x_849_; uint32_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_848_ = lean_unsigned_to_nat(10u);
v___x_849_ = 97;
v___x_850_ = lean_uint32_sub(v_c_843_, v___x_849_);
v___x_851_ = lean_uint32_to_nat(v___x_850_);
v___x_852_ = lean_nat_add(v___x_848_, v___x_851_);
lean_dec(v___x_851_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; uint32_t v___x_854_; uint32_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_853_ = lean_unsigned_to_nat(10u);
v___x_854_ = 65;
v___x_855_ = lean_uint32_sub(v_c_843_, v___x_854_);
v___x_856_ = lean_uint32_to_nat(v___x_855_);
v___x_857_ = lean_nat_add(v___x_853_, v___x_856_);
lean_dec(v___x_856_);
return v___x_857_;
}
}
else
{
uint32_t v___x_858_; uint32_t v___x_859_; lean_object* v___x_860_; 
v___x_858_ = 48;
v___x_859_ = lean_uint32_sub(v_c_843_, v___x_858_);
v___x_860_ = lean_uint32_to_nat(v___x_859_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object* v_c_861_){
_start:
{
uint32_t v_c_boxed_862_; lean_object* v_res_863_; 
v_c_boxed_862_ = lean_unbox_uint32(v_c_861_);
lean_dec(v_c_861_);
v_res_863_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v_c_boxed_862_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object* v___x_864_, lean_object* v___x_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_b_868_){
_start:
{
lean_object* v_startInclusive_869_; lean_object* v_endExclusive_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_startInclusive_869_ = lean_ctor_get(v___x_864_, 1);
v_endExclusive_870_ = lean_ctor_get(v___x_864_, 2);
v___x_871_ = lean_nat_sub(v_endExclusive_870_, v_startInclusive_869_);
v___x_872_ = lean_nat_dec_eq(v_a_867_, v___x_871_);
lean_dec(v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; uint32_t v___x_876_; uint32_t v___x_877_; uint8_t v___x_878_; 
v___x_873_ = lean_nat_add(v___x_865_, v_a_867_);
lean_dec(v_a_867_);
v___x_874_ = lean_string_utf8_next_fast(v_a_866_, v___x_873_);
v___x_875_ = lean_nat_sub(v___x_874_, v___x_865_);
v___x_876_ = lean_string_utf8_get_fast(v_a_866_, v___x_873_);
lean_dec(v___x_873_);
v___x_877_ = 95;
v___x_878_ = lean_uint32_dec_eq(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = lean_unsigned_to_nat(16u);
v___x_880_ = lean_nat_mul(v_b_868_, v___x_879_);
lean_dec(v_b_868_);
v___x_881_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_876_);
v___x_882_ = lean_nat_add(v___x_880_, v___x_881_);
lean_dec(v___x_881_);
lean_dec(v___x_880_);
v_a_867_ = v___x_875_;
v_b_868_ = v___x_882_;
goto _start;
}
else
{
v_a_867_ = v___x_875_;
goto _start;
}
}
else
{
lean_dec(v_a_867_);
return v_b_868_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object* v___x_885_, lean_object* v___x_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_b_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_885_, v___x_886_, v_a_887_, v_a_888_, v_b_889_);
lean_dec_ref(v_a_887_);
lean_dec(v___x_886_);
lean_dec_ref(v___x_885_);
return v_res_890_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3));
v___x_900_ = l_Lean_MessageData_ofFormat(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object* v_x_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_a_906_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
v___x_917_ = l_Lean_Syntax_isLit_x3f(v___x_916_, v_x_901_);
if (lean_obj_tag(v___x_917_) == 1)
{
lean_object* v_val_918_; 
v_val_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_val_918_);
lean_dec_ref(v___x_917_);
v_a_906_ = v_val_918_;
goto v___jp_905_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v___x_917_);
v___x_919_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4);
v___x_920_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_901_, v___x_919_, v_a_902_, v_a_903_);
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
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
v___jp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_unsigned_to_nat(2u);
v___x_909_ = lean_string_utf8_byte_size(v_a_906_);
lean_inc_ref(v_a_906_);
v___x_910_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_910_, 0, v_a_906_);
lean_ctor_set(v___x_910_, 1, v___x_907_);
lean_ctor_set(v___x_910_, 2, v___x_909_);
v___x_911_ = l_String_Slice_Pos_nextn(v___x_910_, v___x_907_, v___x_908_);
lean_dec_ref(v___x_910_);
lean_inc(v___x_911_);
lean_inc_ref(v_a_906_);
v___x_912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_912_, 0, v_a_906_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
lean_ctor_set(v___x_912_, 2, v___x_909_);
v___x_913_ = l_String_Slice_positions(v___x_912_);
v___x_914_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_912_, v___x_911_, v_a_906_, v___x_913_, v___x_907_);
lean_dec_ref(v_a_906_);
lean_dec(v___x_911_);
lean_dec_ref(v___x_912_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object* v_x_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_x_929_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object* v___x_934_, lean_object* v___x_935_, lean_object* v_a_936_, lean_object* v_inst_937_, lean_object* v_R_938_, lean_object* v_a_939_, lean_object* v_b_940_, lean_object* v_c_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_934_, v___x_935_, v_a_936_, v_a_939_, v_b_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object* v___x_943_, lean_object* v___x_944_, lean_object* v_a_945_, lean_object* v_inst_946_, lean_object* v_R_947_, lean_object* v_a_948_, lean_object* v_b_949_, lean_object* v_c_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(v___x_943_, v___x_944_, v_a_945_, v_inst_946_, v_R_947_, v_a_948_, v_b_949_, v_c_950_);
lean_dec_ref(v_a_945_);
lean_dec(v___x_944_);
lean_dec_ref(v___x_943_);
return v_res_951_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5));
v___x_964_ = l_Lean_MessageData_ofFormat(v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object* v_x_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_a_970_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
v___x_983_ = l_Lean_Syntax_isLit_x3f(v___x_982_, v_x_965_);
if (lean_obj_tag(v___x_983_) == 1)
{
lean_object* v_val_984_; 
v_val_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_val_984_);
lean_dec_ref(v___x_983_);
v_a_970_ = v_val_984_;
goto v___jp_969_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec(v___x_983_);
v___x_985_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6);
v___x_986_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_965_, v___x_985_, v_a_966_, v_a_967_);
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
v___jp_969_:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lake_Toml_DateTime_ofString_x3f(v_a_970_);
if (lean_obj_tag(v___x_971_) == 1)
{
lean_object* v_val_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
v_val_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_val_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 0);
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_val_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; 
lean_dec(v___x_971_);
v___x_980_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1);
v___x_981_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_965_, v___x_980_, v_a_966_, v_a_967_);
return v___x_981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object* v_x_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_x_995_);
return v_res_999_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3));
v___x_1009_ = l_Lean_MessageData_ofFormat(v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object* v_x_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_a_1015_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
v___x_1028_ = l_Lean_Syntax_isLit_x3f(v___x_1027_, v_x_1010_);
if (lean_obj_tag(v___x_1028_) == 1)
{
lean_object* v_val_1029_; 
v_val_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_val_1029_);
lean_dec_ref(v___x_1028_);
v_a_1015_ = v_val_1029_;
goto v___jp_1014_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec(v___x_1028_);
v___x_1030_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4);
v___x_1031_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1010_, v___x_1030_, v_a_1011_, v_a_1012_);
return v___x_1031_;
}
v___jp_1014_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_string_utf8_byte_size(v_a_1015_);
lean_inc_ref(v_a_1015_);
v___x_1019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1019_, 0, v_a_1015_);
lean_ctor_set(v___x_1019_, 1, v___x_1017_);
lean_ctor_set(v___x_1019_, 2, v___x_1018_);
v___x_1020_ = l_String_Slice_Pos_nextn(v___x_1019_, v___x_1017_, v___x_1016_);
lean_dec_ref(v___x_1019_);
lean_inc(v___x_1020_);
lean_inc_ref(v_a_1015_);
v___x_1021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1021_, 0, v_a_1015_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
lean_ctor_set(v___x_1021_, 2, v___x_1018_);
v___x_1022_ = lean_nat_sub(v___x_1018_, v___x_1020_);
v___x_1023_ = l_String_Slice_Pos_prevn(v___x_1021_, v___x_1022_, v___x_1016_);
lean_dec_ref(v___x_1021_);
v___x_1024_ = lean_nat_add(v___x_1020_, v___x_1023_);
lean_dec(v___x_1023_);
v___x_1025_ = lean_string_utf8_extract(v_a_1015_, v___x_1020_, v___x_1024_);
lean_dec(v___x_1024_);
lean_dec(v___x_1020_);
lean_dec_ref(v_a_1015_);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object* v_x_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_x_1032_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object* v_msg_1037_){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = l_String_instInhabitedSlice;
v___x_1039_ = lean_panic_fn(v___x_1038_, v_msg_1037_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object* v___y_1040_, lean_object* v_a_1041_, lean_object* v_b_1042_){
_start:
{
lean_object* v_str_1043_; lean_object* v_startInclusive_1044_; lean_object* v_endExclusive_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_str_1043_ = lean_ctor_get(v___y_1040_, 0);
v_startInclusive_1044_ = lean_ctor_get(v___y_1040_, 1);
v_endExclusive_1045_ = lean_ctor_get(v___y_1040_, 2);
v___x_1046_ = lean_nat_sub(v_endExclusive_1045_, v_startInclusive_1044_);
v___x_1047_ = lean_nat_dec_eq(v_a_1041_, v___x_1046_);
lean_dec(v___x_1046_);
if (v___x_1047_ == 0)
{
lean_object* v___x_1048_; uint32_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1048_ = lean_nat_add(v_startInclusive_1044_, v_a_1041_);
lean_dec(v_a_1041_);
v___x_1049_ = lean_string_utf8_get_fast(v_str_1043_, v___x_1048_);
v___x_1050_ = lean_string_utf8_next_fast(v_str_1043_, v___x_1048_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_nat_sub(v___x_1050_, v_startInclusive_1044_);
v___x_1052_ = lean_unsigned_to_nat(16u);
v___x_1053_ = lean_nat_mul(v_b_1042_, v___x_1052_);
lean_dec(v_b_1042_);
v___x_1054_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_1049_);
v___x_1055_ = lean_nat_add(v___x_1053_, v___x_1054_);
lean_dec(v___x_1054_);
lean_dec(v___x_1053_);
v_a_1041_ = v___x_1051_;
v_b_1042_ = v___x_1055_;
goto _start;
}
else
{
lean_dec(v_a_1041_);
return v_b_1042_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object* v___y_1057_, lean_object* v_a_1058_, lean_object* v_b_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1057_, v_a_1058_, v_b_1059_);
lean_dec_ref(v___y_1057_);
return v_res_1060_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1064_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2));
v___x_1065_ = lean_unsigned_to_nat(14u);
v___x_1066_ = lean_unsigned_to_nat(22u);
v___x_1067_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1));
v___x_1068_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0));
v___x_1069_ = l_mkPanicMessageWithDecl(v___x_1068_, v___x_1067_, v___x_1066_, v___x_1065_, v___x_1064_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object* v_s_1070_){
_start:
{
lean_object* v_str_1071_; lean_object* v_startPos_1072_; lean_object* v_stopPos_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1091_; 
v_str_1071_ = lean_ctor_get(v_s_1070_, 0);
v_startPos_1072_ = lean_ctor_get(v_s_1070_, 1);
v_stopPos_1073_ = lean_ctor_get(v_s_1070_, 2);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_s_1070_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1075_ = v_s_1070_;
v_isShared_1076_ = v_isSharedCheck_1091_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_stopPos_1073_);
lean_inc(v_startPos_1072_);
lean_inc(v_str_1071_);
lean_dec(v_s_1070_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1091_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___y_1079_; uint8_t v___x_1085_; 
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1085_ = lean_string_is_valid_pos(v_str_1071_, v_startPos_1072_);
if (v___x_1085_ == 0)
{
lean_del_object(v___x_1075_);
lean_dec(v_stopPos_1073_);
lean_dec(v_startPos_1072_);
lean_dec_ref(v_str_1071_);
goto v___jp_1082_;
}
else
{
uint8_t v___x_1086_; 
v___x_1086_ = lean_string_is_valid_pos(v_str_1071_, v_stopPos_1073_);
if (v___x_1086_ == 0)
{
lean_del_object(v___x_1075_);
lean_dec(v_stopPos_1073_);
lean_dec(v_startPos_1072_);
lean_dec_ref(v_str_1071_);
goto v___jp_1082_;
}
else
{
uint8_t v___x_1087_; 
v___x_1087_ = lean_nat_dec_le(v_startPos_1072_, v_stopPos_1073_);
if (v___x_1087_ == 0)
{
lean_del_object(v___x_1075_);
lean_dec(v_stopPos_1073_);
lean_dec(v_startPos_1072_);
lean_dec_ref(v_str_1071_);
goto v___jp_1082_;
}
else
{
lean_object* v___x_1089_; 
if (v_isShared_1076_ == 0)
{
v___x_1089_ = v___x_1075_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_str_1071_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v_startPos_1072_);
lean_ctor_set(v_reuseFailAlloc_1090_, 2, v_stopPos_1073_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
v___y_1079_ = v___x_1089_;
goto v___jp_1078_;
}
}
}
}
v___jp_1078_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = l_String_Slice_positions(v___y_1079_);
v___x_1081_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1079_, v___x_1080_, v___x_1077_);
lean_dec_ref(v___y_1079_);
return v___x_1081_;
}
v___jp_1082_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3);
v___x_1084_ = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(v___x_1083_);
v___y_1079_ = v___x_1084_;
goto v___jp_1078_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object* v___y_1092_, lean_object* v_inst_1093_, lean_object* v_R_1094_, lean_object* v_a_1095_, lean_object* v_b_1096_, lean_object* v_c_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1092_, v_a_1095_, v_b_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object* v___y_1099_, lean_object* v_inst_1100_, lean_object* v_R_1101_, lean_object* v_a_1102_, lean_object* v_b_1103_, lean_object* v_c_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(v___y_1099_, v_inst_1100_, v_R_1101_, v_a_1102_, v_b_1103_, v_c_1104_);
lean_dec_ref(v___y_1099_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object* v_s_1106_, lean_object* v_stopPos_1107_, lean_object* v_i_1108_){
_start:
{
uint8_t v___y_1113_; uint8_t v___x_1114_; 
v___x_1114_ = l_String_instDecidableLtRaw___aux__1(v_i_1108_, v_stopPos_1107_);
if (v___x_1114_ == 0)
{
return v_i_1108_;
}
else
{
uint32_t v___x_1115_; uint8_t v___y_1117_; uint32_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1115_ = lean_string_utf8_get(v_s_1106_, v_i_1108_);
v___x_1122_ = 32;
v___x_1123_ = lean_uint32_dec_eq(v___x_1115_, v___x_1122_);
if (v___x_1123_ == 0)
{
uint32_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = 9;
v___x_1125_ = lean_uint32_dec_eq(v___x_1115_, v___x_1124_);
v___y_1117_ = v___x_1125_;
goto v___jp_1116_;
}
else
{
v___y_1117_ = v___x_1123_;
goto v___jp_1116_;
}
v___jp_1116_:
{
if (v___y_1117_ == 0)
{
uint32_t v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = 13;
v___x_1119_ = lean_uint32_dec_eq(v___x_1115_, v___x_1118_);
if (v___x_1119_ == 0)
{
uint32_t v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = 10;
v___x_1121_ = lean_uint32_dec_eq(v___x_1115_, v___x_1120_);
v___y_1113_ = v___x_1121_;
goto v___jp_1112_;
}
else
{
v___y_1113_ = v___x_1119_;
goto v___jp_1112_;
}
}
else
{
goto v___jp_1109_;
}
}
}
v___jp_1109_:
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_string_utf8_next(v_s_1106_, v_i_1108_);
lean_dec(v_i_1108_);
v_i_1108_ = v___x_1110_;
goto _start;
}
v___jp_1112_:
{
if (v___y_1113_ == 0)
{
return v_i_1108_;
}
else
{
goto v___jp_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object* v_s_1126_, lean_object* v_stopPos_1127_, lean_object* v_i_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_s_1126_, v_stopPos_1127_, v_i_1128_);
lean_dec(v_stopPos_1127_);
lean_dec_ref(v_s_1126_);
return v_res_1129_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1(void){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0));
v___x_1132_ = l_Lean_stringToMessageData(v___x_1131_);
return v___x_1132_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object* v_lit_1136_, lean_object* v_i_1137_, lean_object* v_out_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v_escape_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; uint8_t v___x_1174_; 
v___x_1174_ = lean_string_utf8_at_end(v_lit_1136_, v_i_1137_);
if (v___x_1174_ == 0)
{
uint32_t v_curr_1175_; lean_object* v_i_1176_; uint32_t v___x_1177_; uint8_t v___x_1178_; 
v_curr_1175_ = lean_string_utf8_get_fast(v_lit_1136_, v_i_1137_);
v_i_1176_ = lean_string_utf8_next_fast(v_lit_1136_, v_i_1137_);
lean_dec(v_i_1137_);
v___x_1177_ = 92;
v___x_1178_ = lean_uint32_dec_eq(v_curr_1175_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_string_push(v_out_1138_, v_curr_1175_);
v_i_1137_ = v_i_1176_;
v_out_1138_ = v___x_1179_;
goto _start;
}
else
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_string_utf8_at_end(v_lit_1136_, v_i_1176_);
if (v___x_1181_ == 0)
{
uint32_t v_curr_1182_; lean_object* v_next_1183_; uint32_t v___x_1184_; uint8_t v___x_1185_; 
v_curr_1182_ = lean_string_utf8_get_fast(v_lit_1136_, v_i_1176_);
v_next_1183_ = lean_string_utf8_next_fast(v_lit_1136_, v_i_1176_);
v___x_1184_ = 98;
v___x_1185_ = lean_uint32_dec_eq(v_curr_1182_, v___x_1184_);
if (v___x_1185_ == 0)
{
uint32_t v___x_1186_; uint8_t v___x_1187_; 
v___x_1186_ = 116;
v___x_1187_ = lean_uint32_dec_eq(v_curr_1182_, v___x_1186_);
if (v___x_1187_ == 0)
{
uint32_t v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = 110;
v___x_1189_ = lean_uint32_dec_eq(v_curr_1182_, v___x_1188_);
if (v___x_1189_ == 0)
{
uint32_t v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = 102;
v___x_1191_ = lean_uint32_dec_eq(v_curr_1182_, v___x_1190_);
if (v___x_1191_ == 0)
{
uint32_t v___x_1192_; uint8_t v___x_1193_; 
v___x_1192_ = 114;
v___x_1193_ = lean_uint32_dec_eq(v_curr_1182_, v___x_1192_);
if (v___x_1193_ == 0)
{
uint32_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 34;
v___x_1195_ = lean_uint32_dec_eq(v_curr_1182_, v___x_1194_);
if (v___x_1195_ == 0)
{
uint8_t v___x_1196_; 
v___x_1196_ = lean_uint32_dec_eq(v_curr_1182_, v___x_1177_);
if (v___x_1196_ == 0)
{
uint32_t v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = 117;
v___x_1198_ = lean_uint32_dec_eq(v_curr_1182_, v___x_1197_);
if (v___x_1198_ == 0)
{
uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1199_ = 85;
v___x_1200_ = lean_uint32_dec_eq(v_curr_1182_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; lean_object* v_b_1202_; 
v___x_1201_ = lean_string_utf8_byte_size(v_lit_1136_);
v_b_1202_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_lit_1136_, v___x_1201_, v_i_1176_);
v_i_1137_ = v_b_1202_;
goto _start;
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1204_ = lean_string_utf8_byte_size(v_lit_1136_);
lean_inc_ref(v_lit_1136_);
v___x_1205_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1205_, 0, v_lit_1136_);
lean_ctor_set(v___x_1205_, 1, v_next_1183_);
lean_ctor_set(v___x_1205_, 2, v___x_1204_);
v___x_1206_ = lean_unsigned_to_nat(8u);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = l_Substring_Raw_nextn(v___x_1205_, v___x_1206_, v___x_1207_);
lean_dec_ref(v___x_1205_);
v___x_1209_ = lean_nat_add(v_next_1183_, v___x_1208_);
lean_dec(v___x_1208_);
lean_inc_ref(v_lit_1136_);
v___x_1210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1210_, 0, v_lit_1136_);
lean_ctor_set(v___x_1210_, 1, v_next_1183_);
lean_ctor_set(v___x_1210_, 2, v___x_1209_);
v_escape_1164_ = v___x_1210_;
v___y_1165_ = v_a_1139_;
v___y_1166_ = v_a_1140_;
goto v___jp_1163_;
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1211_ = lean_string_utf8_byte_size(v_lit_1136_);
lean_inc_ref(v_lit_1136_);
v___x_1212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1212_, 0, v_lit_1136_);
lean_ctor_set(v___x_1212_, 1, v_next_1183_);
lean_ctor_set(v___x_1212_, 2, v___x_1211_);
v___x_1213_ = lean_unsigned_to_nat(4u);
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = l_Substring_Raw_nextn(v___x_1212_, v___x_1213_, v___x_1214_);
lean_dec_ref(v___x_1212_);
v___x_1216_ = lean_nat_add(v_next_1183_, v___x_1215_);
lean_dec(v___x_1215_);
lean_inc_ref(v_lit_1136_);
v___x_1217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1217_, 0, v_lit_1136_);
lean_ctor_set(v___x_1217_, 1, v_next_1183_);
lean_ctor_set(v___x_1217_, 2, v___x_1216_);
v_escape_1164_ = v___x_1217_;
v___y_1165_ = v_a_1139_;
v___y_1166_ = v_a_1140_;
goto v___jp_1163_;
}
}
else
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_string_push(v_out_1138_, v___x_1177_);
v_i_1137_ = v_next_1183_;
v_out_1138_ = v___x_1218_;
goto _start;
}
}
else
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_string_push(v_out_1138_, v___x_1194_);
v_i_1137_ = v_next_1183_;
v_out_1138_ = v___x_1220_;
goto _start;
}
}
else
{
uint32_t v___x_1222_; lean_object* v___x_1223_; 
v___x_1222_ = 13;
v___x_1223_ = lean_string_push(v_out_1138_, v___x_1222_);
v_i_1137_ = v_next_1183_;
v_out_1138_ = v___x_1223_;
goto _start;
}
}
else
{
uint32_t v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = 12;
v___x_1226_ = lean_string_push(v_out_1138_, v___x_1225_);
v_i_1137_ = v_next_1183_;
v_out_1138_ = v___x_1226_;
goto _start;
}
}
else
{
uint32_t v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = 10;
v___x_1229_ = lean_string_push(v_out_1138_, v___x_1228_);
v_i_1137_ = v_next_1183_;
v_out_1138_ = v___x_1229_;
goto _start;
}
}
else
{
uint32_t v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = 9;
v___x_1232_ = lean_string_push(v_out_1138_, v___x_1231_);
v_i_1137_ = v_next_1183_;
v_out_1138_ = v___x_1232_;
goto _start;
}
}
else
{
uint32_t v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = 8;
v___x_1235_ = lean_string_push(v_out_1138_, v___x_1234_);
v_i_1137_ = v_next_1183_;
v_out_1138_ = v___x_1235_;
goto _start;
}
}
else
{
lean_object* v___x_1237_; 
lean_dec_ref(v_lit_1136_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_out_1138_);
return v___x_1237_;
}
}
}
else
{
lean_object* v___x_1238_; 
lean_dec(v_i_1137_);
lean_dec_ref(v_lit_1136_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_out_1138_);
return v___x_1238_;
}
v___jp_1142_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1146_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1);
v___x_1147_ = lean_substring_tostring(v___y_1144_);
v___x_1148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
v___x_1149_ = l_Lean_MessageData_ofFormat(v___x_1148_);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1146_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v___x_1152_, v___y_1143_, v___y_1145_);
return v___x_1153_;
}
v___jp_1154_:
{
lean_object* v_stopPos_1159_; uint32_t v_ch_1160_; lean_object* v___x_1161_; 
v_stopPos_1159_ = lean_ctor_get(v___y_1156_, 2);
lean_inc(v_stopPos_1159_);
lean_dec_ref(v___y_1156_);
v_ch_1160_ = lean_uint32_of_nat(v___y_1158_);
lean_dec(v___y_1158_);
v___x_1161_ = lean_string_push(v_out_1138_, v_ch_1160_);
v_i_1137_ = v_stopPos_1159_;
v_out_1138_ = v___x_1161_;
v_a_1139_ = v___y_1155_;
v_a_1140_ = v___y_1157_;
goto _start;
}
v___jp_1163_:
{
lean_object* v_val_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
lean_inc_ref(v_escape_1164_);
v_val_1167_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(v_escape_1164_);
v___x_1168_ = lean_unsigned_to_nat(55296u);
v___x_1169_ = lean_nat_dec_lt(v_val_1167_, v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_unsigned_to_nat(57343u);
v___x_1171_ = lean_nat_dec_lt(v___x_1170_, v_val_1167_);
if (v___x_1171_ == 0)
{
lean_dec(v_val_1167_);
lean_dec_ref(v_out_1138_);
lean_dec_ref(v_lit_1136_);
v___y_1143_ = v___y_1165_;
v___y_1144_ = v_escape_1164_;
v___y_1145_ = v___y_1166_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = lean_unsigned_to_nat(1114112u);
v___x_1173_ = lean_nat_dec_lt(v_val_1167_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec(v_val_1167_);
lean_dec_ref(v_out_1138_);
lean_dec_ref(v_lit_1136_);
v___y_1143_ = v___y_1165_;
v___y_1144_ = v_escape_1164_;
v___y_1145_ = v___y_1166_;
goto v___jp_1142_;
}
else
{
v___y_1155_ = v___y_1165_;
v___y_1156_ = v_escape_1164_;
v___y_1157_ = v___y_1166_;
v___y_1158_ = v_val_1167_;
goto v___jp_1154_;
}
}
}
else
{
v___y_1155_ = v___y_1165_;
v___y_1156_ = v_escape_1164_;
v___y_1157_ = v___y_1166_;
v___y_1158_ = v_val_1167_;
goto v___jp_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object* v_lit_1239_, lean_object* v_i_1240_, lean_object* v_out_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v_lit_1239_, v_i_1240_, v_out_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
return v_res_1245_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4));
v___x_1256_ = l_Lean_MessageData_ofFormat(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object* v_x_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_a_1262_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
v___x_1294_ = l_Lean_Syntax_isLit_x3f(v___x_1293_, v_x_1257_);
if (lean_obj_tag(v___x_1294_) == 1)
{
lean_object* v_val_1295_; 
v_val_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_val_1295_);
lean_dec_ref(v___x_1294_);
v_a_1262_ = v_val_1295_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec(v___x_1294_);
v___x_1296_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5);
v___x_1297_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1257_, v___x_1296_, v_a_1258_, v_a_1259_);
return v___x_1297_;
}
v___jp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_fileName_1266_; lean_object* v_fileMap_1267_; lean_object* v_options_1268_; lean_object* v_currRecDepth_1269_; lean_object* v_maxRecDepth_1270_; lean_object* v_ref_1271_; lean_object* v_currNamespace_1272_; lean_object* v_openDecls_1273_; lean_object* v_initHeartbeats_1274_; lean_object* v_maxHeartbeats_1275_; lean_object* v_quotContext_1276_; lean_object* v_currMacroScope_1277_; uint8_t v_diag_1278_; lean_object* v_cancelTk_x3f_1279_; uint8_t v_suppressElabErrors_1280_; lean_object* v_inheritedTraceOptions_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v_ref_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_string_utf8_byte_size(v_a_1262_);
lean_inc_ref(v_a_1262_);
v___x_1265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1265_, 0, v_a_1262_);
lean_ctor_set(v___x_1265_, 1, v___x_1263_);
lean_ctor_set(v___x_1265_, 2, v___x_1264_);
v_fileName_1266_ = lean_ctor_get(v_a_1258_, 0);
v_fileMap_1267_ = lean_ctor_get(v_a_1258_, 1);
v_options_1268_ = lean_ctor_get(v_a_1258_, 2);
v_currRecDepth_1269_ = lean_ctor_get(v_a_1258_, 3);
v_maxRecDepth_1270_ = lean_ctor_get(v_a_1258_, 4);
v_ref_1271_ = lean_ctor_get(v_a_1258_, 5);
v_currNamespace_1272_ = lean_ctor_get(v_a_1258_, 6);
v_openDecls_1273_ = lean_ctor_get(v_a_1258_, 7);
v_initHeartbeats_1274_ = lean_ctor_get(v_a_1258_, 8);
v_maxHeartbeats_1275_ = lean_ctor_get(v_a_1258_, 9);
v_quotContext_1276_ = lean_ctor_get(v_a_1258_, 10);
v_currMacroScope_1277_ = lean_ctor_get(v_a_1258_, 11);
v_diag_1278_ = lean_ctor_get_uint8(v_a_1258_, sizeof(void*)*14);
v_cancelTk_x3f_1279_ = lean_ctor_get(v_a_1258_, 12);
v_suppressElabErrors_1280_ = lean_ctor_get_uint8(v_a_1258_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1281_ = lean_ctor_get(v_a_1258_, 13);
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = l_String_Slice_Pos_nextn(v___x_1265_, v___x_1263_, v___x_1282_);
lean_dec_ref(v___x_1265_);
lean_inc(v___x_1283_);
lean_inc_ref(v_a_1262_);
v___x_1284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1284_, 0, v_a_1262_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
lean_ctor_set(v___x_1284_, 2, v___x_1264_);
v___x_1285_ = lean_nat_sub(v___x_1264_, v___x_1283_);
v___x_1286_ = l_String_Slice_Pos_prevn(v___x_1284_, v___x_1285_, v___x_1282_);
lean_dec_ref(v___x_1284_);
v___x_1287_ = lean_nat_add(v___x_1283_, v___x_1286_);
lean_dec(v___x_1286_);
v___x_1288_ = lean_string_utf8_extract(v_a_1262_, v___x_1283_, v___x_1287_);
lean_dec(v___x_1287_);
lean_dec(v___x_1283_);
lean_dec_ref(v_a_1262_);
v___x_1289_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1290_ = l_Lean_replaceRef(v_x_1257_, v_ref_1271_);
lean_inc_ref(v_inheritedTraceOptions_1281_);
lean_inc(v_cancelTk_x3f_1279_);
lean_inc(v_currMacroScope_1277_);
lean_inc(v_quotContext_1276_);
lean_inc(v_maxHeartbeats_1275_);
lean_inc(v_initHeartbeats_1274_);
lean_inc(v_openDecls_1273_);
lean_inc(v_currNamespace_1272_);
lean_inc(v_maxRecDepth_1270_);
lean_inc(v_currRecDepth_1269_);
lean_inc_ref(v_options_1268_);
lean_inc_ref(v_fileMap_1267_);
lean_inc_ref(v_fileName_1266_);
v___x_1291_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1291_, 0, v_fileName_1266_);
lean_ctor_set(v___x_1291_, 1, v_fileMap_1267_);
lean_ctor_set(v___x_1291_, 2, v_options_1268_);
lean_ctor_set(v___x_1291_, 3, v_currRecDepth_1269_);
lean_ctor_set(v___x_1291_, 4, v_maxRecDepth_1270_);
lean_ctor_set(v___x_1291_, 5, v_ref_1290_);
lean_ctor_set(v___x_1291_, 6, v_currNamespace_1272_);
lean_ctor_set(v___x_1291_, 7, v_openDecls_1273_);
lean_ctor_set(v___x_1291_, 8, v_initHeartbeats_1274_);
lean_ctor_set(v___x_1291_, 9, v_maxHeartbeats_1275_);
lean_ctor_set(v___x_1291_, 10, v_quotContext_1276_);
lean_ctor_set(v___x_1291_, 11, v_currMacroScope_1277_);
lean_ctor_set(v___x_1291_, 12, v_cancelTk_x3f_1279_);
lean_ctor_set(v___x_1291_, 13, v_inheritedTraceOptions_1281_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*14, v_diag_1278_);
lean_ctor_set_uint8(v___x_1291_, sizeof(void*)*14 + 1, v_suppressElabErrors_1280_);
v___x_1292_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1288_, v___x_1263_, v___x_1289_, v___x_1291_, v_a_1259_);
lean_dec_ref(v___x_1291_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object* v_x_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_x_1298_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object* v_s_1303_){
_start:
{
uint32_t v___y_1305_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1322_ = lean_unsigned_to_nat(0u);
v___x_1323_ = lean_string_utf8_byte_size(v_s_1303_);
lean_inc_ref(v_s_1303_);
v___x_1324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1324_, 0, v_s_1303_);
lean_ctor_set(v___x_1324_, 1, v___x_1322_);
lean_ctor_set(v___x_1324_, 2, v___x_1323_);
v___x_1325_ = l_String_Slice_Pos_get_x3f(v___x_1324_, v___x_1322_);
lean_dec_ref(v___x_1324_);
if (lean_obj_tag(v___x_1325_) == 0)
{
uint32_t v___x_1326_; 
v___x_1326_ = 65;
v___y_1305_ = v___x_1326_;
goto v___jp_1304_;
}
else
{
lean_object* v_val_1327_; uint32_t v___x_1328_; 
v_val_1327_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_val_1327_);
lean_dec_ref(v___x_1325_);
v___x_1328_ = lean_unbox_uint32(v_val_1327_);
lean_dec(v_val_1327_);
v___y_1305_ = v___x_1328_;
goto v___jp_1304_;
}
v___jp_1304_:
{
uint32_t v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = 13;
v___x_1307_ = lean_uint32_dec_eq(v___y_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
uint32_t v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = 10;
v___x_1309_ = lean_uint32_dec_eq(v___y_1305_, v___x_1308_);
if (v___x_1309_ == 0)
{
return v_s_1303_;
}
else
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1310_ = lean_unsigned_to_nat(1u);
v___x_1311_ = lean_unsigned_to_nat(0u);
v___x_1312_ = lean_string_utf8_byte_size(v_s_1303_);
lean_inc_ref(v_s_1303_);
v___x_1313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1313_, 0, v_s_1303_);
lean_ctor_set(v___x_1313_, 1, v___x_1311_);
lean_ctor_set(v___x_1313_, 2, v___x_1312_);
v___x_1314_ = l_String_Slice_Pos_nextn(v___x_1313_, v___x_1311_, v___x_1310_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = lean_string_utf8_extract(v_s_1303_, v___x_1314_, v___x_1312_);
lean_dec(v___x_1314_);
lean_dec_ref(v_s_1303_);
return v___x_1315_;
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1316_ = lean_unsigned_to_nat(2u);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_string_utf8_byte_size(v_s_1303_);
lean_inc_ref(v_s_1303_);
v___x_1319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1319_, 0, v_s_1303_);
lean_ctor_set(v___x_1319_, 1, v___x_1317_);
lean_ctor_set(v___x_1319_, 2, v___x_1318_);
v___x_1320_ = l_String_Slice_Pos_nextn(v___x_1319_, v___x_1317_, v___x_1316_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = lean_string_utf8_extract(v_s_1303_, v___x_1320_, v___x_1318_);
lean_dec(v___x_1320_);
lean_dec_ref(v_s_1303_);
return v___x_1321_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3));
v___x_1338_ = l_Lean_MessageData_ofFormat(v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object* v_x_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_a_1344_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
v___x_1358_ = l_Lean_Syntax_isLit_x3f(v___x_1357_, v_x_1339_);
if (lean_obj_tag(v___x_1358_) == 1)
{
lean_object* v_val_1359_; 
v_val_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_val_1359_);
lean_dec_ref(v___x_1358_);
v_a_1344_ = v_val_1359_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec(v___x_1358_);
v___x_1360_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4);
v___x_1361_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1339_, v___x_1360_, v_a_1340_, v_a_1341_);
return v___x_1361_;
}
v___jp_1343_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1345_ = lean_unsigned_to_nat(3u);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_string_utf8_byte_size(v_a_1344_);
lean_inc_ref(v_a_1344_);
v___x_1348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1348_, 0, v_a_1344_);
lean_ctor_set(v___x_1348_, 1, v___x_1346_);
lean_ctor_set(v___x_1348_, 2, v___x_1347_);
v___x_1349_ = l_String_Slice_Pos_nextn(v___x_1348_, v___x_1346_, v___x_1345_);
lean_dec_ref(v___x_1348_);
lean_inc(v___x_1349_);
lean_inc_ref(v_a_1344_);
v___x_1350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1350_, 0, v_a_1344_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
lean_ctor_set(v___x_1350_, 2, v___x_1347_);
v___x_1351_ = lean_nat_sub(v___x_1347_, v___x_1349_);
v___x_1352_ = l_String_Slice_Pos_prevn(v___x_1350_, v___x_1351_, v___x_1345_);
lean_dec_ref(v___x_1350_);
v___x_1353_ = lean_nat_add(v___x_1349_, v___x_1352_);
lean_dec(v___x_1352_);
v___x_1354_ = lean_string_utf8_extract(v_a_1344_, v___x_1349_, v___x_1353_);
lean_dec(v___x_1353_);
lean_dec(v___x_1349_);
lean_dec_ref(v_a_1344_);
v___x_1355_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object* v_x_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1362_, v_a_1363_, v_a_1364_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_x_1362_);
return v_res_1366_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3));
v___x_1376_ = l_Lean_MessageData_ofFormat(v___x_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object* v_x_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_a_1382_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
v___x_1415_ = l_Lean_Syntax_isLit_x3f(v___x_1414_, v_x_1377_);
if (lean_obj_tag(v___x_1415_) == 1)
{
lean_object* v_val_1416_; 
v_val_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_val_1416_);
lean_dec_ref(v___x_1415_);
v_a_1382_ = v_val_1416_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec(v___x_1415_);
v___x_1417_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4);
v___x_1418_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1377_, v___x_1417_, v_a_1378_, v_a_1379_);
return v___x_1418_;
}
v___jp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_fileName_1386_; lean_object* v_fileMap_1387_; lean_object* v_options_1388_; lean_object* v_currRecDepth_1389_; lean_object* v_maxRecDepth_1390_; lean_object* v_ref_1391_; lean_object* v_currNamespace_1392_; lean_object* v_openDecls_1393_; lean_object* v_initHeartbeats_1394_; lean_object* v_maxHeartbeats_1395_; lean_object* v_quotContext_1396_; lean_object* v_currMacroScope_1397_; uint8_t v_diag_1398_; lean_object* v_cancelTk_x3f_1399_; uint8_t v_suppressElabErrors_1400_; lean_object* v_inheritedTraceOptions_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_ref_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = lean_string_utf8_byte_size(v_a_1382_);
lean_inc_ref(v_a_1382_);
v___x_1385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1385_, 0, v_a_1382_);
lean_ctor_set(v___x_1385_, 1, v___x_1383_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
v_fileName_1386_ = lean_ctor_get(v_a_1378_, 0);
v_fileMap_1387_ = lean_ctor_get(v_a_1378_, 1);
v_options_1388_ = lean_ctor_get(v_a_1378_, 2);
v_currRecDepth_1389_ = lean_ctor_get(v_a_1378_, 3);
v_maxRecDepth_1390_ = lean_ctor_get(v_a_1378_, 4);
v_ref_1391_ = lean_ctor_get(v_a_1378_, 5);
v_currNamespace_1392_ = lean_ctor_get(v_a_1378_, 6);
v_openDecls_1393_ = lean_ctor_get(v_a_1378_, 7);
v_initHeartbeats_1394_ = lean_ctor_get(v_a_1378_, 8);
v_maxHeartbeats_1395_ = lean_ctor_get(v_a_1378_, 9);
v_quotContext_1396_ = lean_ctor_get(v_a_1378_, 10);
v_currMacroScope_1397_ = lean_ctor_get(v_a_1378_, 11);
v_diag_1398_ = lean_ctor_get_uint8(v_a_1378_, sizeof(void*)*14);
v_cancelTk_x3f_1399_ = lean_ctor_get(v_a_1378_, 12);
v_suppressElabErrors_1400_ = lean_ctor_get_uint8(v_a_1378_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1401_ = lean_ctor_get(v_a_1378_, 13);
v___x_1402_ = lean_unsigned_to_nat(3u);
v___x_1403_ = l_String_Slice_Pos_nextn(v___x_1385_, v___x_1383_, v___x_1402_);
lean_dec_ref(v___x_1385_);
lean_inc(v___x_1403_);
lean_inc_ref(v_a_1382_);
v___x_1404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1404_, 0, v_a_1382_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
lean_ctor_set(v___x_1404_, 2, v___x_1384_);
v___x_1405_ = lean_nat_sub(v___x_1384_, v___x_1403_);
v___x_1406_ = l_String_Slice_Pos_prevn(v___x_1404_, v___x_1405_, v___x_1402_);
lean_dec_ref(v___x_1404_);
v___x_1407_ = lean_nat_add(v___x_1403_, v___x_1406_);
lean_dec(v___x_1406_);
v___x_1408_ = lean_string_utf8_extract(v_a_1382_, v___x_1403_, v___x_1407_);
lean_dec(v___x_1407_);
lean_dec(v___x_1403_);
lean_dec_ref(v_a_1382_);
v___x_1409_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1408_);
v___x_1410_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1411_ = l_Lean_replaceRef(v_x_1377_, v_ref_1391_);
lean_inc_ref(v_inheritedTraceOptions_1401_);
lean_inc(v_cancelTk_x3f_1399_);
lean_inc(v_currMacroScope_1397_);
lean_inc(v_quotContext_1396_);
lean_inc(v_maxHeartbeats_1395_);
lean_inc(v_initHeartbeats_1394_);
lean_inc(v_openDecls_1393_);
lean_inc(v_currNamespace_1392_);
lean_inc(v_maxRecDepth_1390_);
lean_inc(v_currRecDepth_1389_);
lean_inc_ref(v_options_1388_);
lean_inc_ref(v_fileMap_1387_);
lean_inc_ref(v_fileName_1386_);
v___x_1412_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1412_, 0, v_fileName_1386_);
lean_ctor_set(v___x_1412_, 1, v_fileMap_1387_);
lean_ctor_set(v___x_1412_, 2, v_options_1388_);
lean_ctor_set(v___x_1412_, 3, v_currRecDepth_1389_);
lean_ctor_set(v___x_1412_, 4, v_maxRecDepth_1390_);
lean_ctor_set(v___x_1412_, 5, v_ref_1411_);
lean_ctor_set(v___x_1412_, 6, v_currNamespace_1392_);
lean_ctor_set(v___x_1412_, 7, v_openDecls_1393_);
lean_ctor_set(v___x_1412_, 8, v_initHeartbeats_1394_);
lean_ctor_set(v___x_1412_, 9, v_maxHeartbeats_1395_);
lean_ctor_set(v___x_1412_, 10, v_quotContext_1396_);
lean_ctor_set(v___x_1412_, 11, v_currMacroScope_1397_);
lean_ctor_set(v___x_1412_, 12, v_cancelTk_x3f_1399_);
lean_ctor_set(v___x_1412_, 13, v_inheritedTraceOptions_1401_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*14, v_diag_1398_);
lean_ctor_set_uint8(v___x_1412_, sizeof(void*)*14 + 1, v_suppressElabErrors_1400_);
v___x_1413_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1409_, v___x_1383_, v___x_1410_, v___x_1412_, v_a_1379_);
lean_dec_ref(v___x_1412_);
return v___x_1413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object* v_x_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1419_, v_a_1420_, v_a_1421_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_x_1419_);
return v_res_1423_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2));
v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object* v_x_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_1432_);
v___x_1437_ = l_Lean_Syntax_isOfKind(v_x_1432_, v___x_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1439_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1432_, v___x_1438_, v_a_1433_, v_a_1434_);
lean_dec(v_x_1432_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; lean_object* v_x_1441_; lean_object* v___x_1442_; uint8_t v___x_1443_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v_x_1441_ = l_Lean_Syntax_getArg(v_x_1432_, v___x_1440_);
v___x_1442_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1441_);
v___x_1443_ = l_Lean_Syntax_isOfKind(v_x_1441_, v___x_1442_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1441_);
v___x_1445_ = l_Lean_Syntax_isOfKind(v_x_1441_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
lean_inc(v_x_1441_);
v___x_1447_ = l_Lean_Syntax_isOfKind(v_x_1441_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
lean_inc(v_x_1441_);
v___x_1449_ = l_Lean_Syntax_isOfKind(v_x_1441_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
lean_dec(v_x_1441_);
v___x_1450_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1451_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1432_, v___x_1450_, v_a_1433_, v_a_1434_);
lean_dec(v_x_1432_);
return v___x_1451_;
}
else
{
lean_object* v___x_1452_; 
lean_dec(v_x_1432_);
v___x_1452_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1441_, v_a_1433_, v_a_1434_);
lean_dec(v_x_1441_);
return v___x_1452_;
}
}
else
{
lean_object* v___x_1453_; 
lean_dec(v_x_1432_);
v___x_1453_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1441_, v_a_1433_, v_a_1434_);
lean_dec(v_x_1441_);
return v___x_1453_;
}
}
else
{
lean_object* v___x_1454_; 
lean_dec(v_x_1432_);
v___x_1454_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1441_, v_a_1433_, v_a_1434_);
lean_dec(v_x_1441_);
return v___x_1454_;
}
}
else
{
lean_object* v___x_1455_; 
lean_dec(v_x_1432_);
v___x_1455_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1441_, v_a_1433_, v_a_1434_);
lean_dec(v_x_1441_);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object* v_x_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_1456_, v_a_1457_, v_a_1458_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
return v_res_1460_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3));
v___x_1470_ = l_Lean_MessageData_ofFormat(v___x_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object* v_x_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v___x_1475_; lean_object* v_toApplicative_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1521_; 
v___x_1475_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; 
v_unused_1522_ = lean_ctor_get(v___x_1475_, 1);
lean_dec(v_unused_1522_);
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1521_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_toApplicative_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1521_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v_toFunctor_1480_; lean_object* v_toSeq_1481_; lean_object* v_toSeqLeft_1482_; lean_object* v_toSeqRight_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1519_; 
v_toFunctor_1480_ = lean_ctor_get(v_toApplicative_1476_, 0);
v_toSeq_1481_ = lean_ctor_get(v_toApplicative_1476_, 2);
v_toSeqLeft_1482_ = lean_ctor_get(v_toApplicative_1476_, 3);
v_toSeqRight_1483_ = lean_ctor_get(v_toApplicative_1476_, 4);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_toApplicative_1476_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_toApplicative_1476_, 1);
lean_dec(v_unused_1520_);
v___x_1485_ = v_toApplicative_1476_;
v_isShared_1486_ = v_isSharedCheck_1519_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_toSeqRight_1483_);
lean_inc(v_toSeqLeft_1482_);
lean_inc(v_toSeq_1481_);
lean_inc(v_toFunctor_1480_);
lean_dec(v_toApplicative_1476_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1519_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___f_1488_; lean_object* v___f_1489_; lean_object* v___f_1490_; lean_object* v___f_1491_; lean_object* v___x_1492_; lean_object* v___f_1493_; lean_object* v___f_1494_; lean_object* v___f_1495_; lean_object* v___x_1497_; 
v___x_1487_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
v___f_1488_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_1489_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref(v_toFunctor_1480_);
v___f_1490_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1490_, 0, v_toFunctor_1480_);
v___f_1491_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1491_, 0, v_toFunctor_1480_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___f_1490_);
lean_ctor_set(v___x_1492_, 1, v___f_1491_);
v___f_1493_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1493_, 0, v_toSeqRight_1483_);
v___f_1494_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1494_, 0, v_toSeqLeft_1482_);
v___f_1495_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1495_, 0, v_toSeq_1481_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 4, v___f_1493_);
lean_ctor_set(v___x_1485_, 3, v___f_1494_);
lean_ctor_set(v___x_1485_, 2, v___f_1495_);
lean_ctor_set(v___x_1485_, 1, v___f_1488_);
lean_ctor_set(v___x_1485_, 0, v___x_1492_);
v___x_1497_ = v___x_1485_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___f_1488_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v___f_1495_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v___f_1494_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v___f_1493_);
v___x_1497_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 1, v___f_1489_);
lean_ctor_set(v___x_1478_, 0, v___x_1497_);
v___x_1499_ = v___x_1478_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___f_1489_);
v___x_1499_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1500_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_1501_ = l_Lean_Core_instMonadRefCoreM;
v___x_1502_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_1499_);
v___x_1503_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1502_, v___x_1499_);
v___x_1504_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1500_);
lean_ctor_set(v___x_1504_, 1, v___x_1501_);
lean_ctor_set(v___x_1504_, 2, v___x_1503_);
v___x_1505_ = l_Lean_Syntax_isLit_x3f(v___x_1487_, v_x_1471_);
if (lean_obj_tag(v___x_1505_) == 1)
{
lean_object* v_val_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v___x_1504_);
lean_dec_ref(v___x_1499_);
lean_dec(v_x_1471_);
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_val_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_val_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
else
{
lean_object* v___x_1514_; lean_object* v___x_25__overap_1515_; lean_object* v___x_1516_; 
lean_dec(v___x_1505_);
v___x_1514_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_25__overap_1515_ = l_Lean_throwErrorAt___redArg(v___x_1499_, v___x_1504_, v_x_1471_, v___x_1514_);
lean_inc(v_a_1473_);
lean_inc_ref(v_a_1472_);
v___x_1516_ = lean_apply_3(v___x_25__overap_1515_, v_a_1472_, v_a_1473_, lean_box(0));
return v___x_1516_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object* v_x_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(v_x_1523_, v_a_1524_, v_a_1525_);
lean_dec(v_a_1525_);
lean_dec_ref(v_a_1524_);
return v_res_1527_;
}
}
static lean_object* _init_l_Lake_Toml_elabSimpleKey___closed__3(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__2));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object* v_x_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__1));
lean_inc(v_x_1536_);
v___x_1541_ = l_Lean_Syntax_isOfKind(v_x_1536_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1543_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1536_, v___x_1542_, v_a_1537_, v_a_1538_);
lean_dec(v_x_1536_);
return v___x_1543_;
}
else
{
lean_object* v___x_1544_; lean_object* v_x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1544_ = lean_unsigned_to_nat(0u);
v_x_1545_ = l_Lean_Syntax_getArg(v_x_1536_, v___x_1544_);
v___x_1546_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
lean_inc(v_x_1545_);
v___x_1547_ = l_Lean_Syntax_isOfKind(v_x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1548_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1545_);
v___x_1549_ = l_Lean_Syntax_isOfKind(v_x_1545_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1545_);
v___x_1551_ = l_Lean_Syntax_isOfKind(v_x_1545_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec(v_x_1545_);
v___x_1552_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1553_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1536_, v___x_1552_, v_a_1537_, v_a_1538_);
lean_dec(v_x_1536_);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; 
lean_dec(v_x_1536_);
v___x_1554_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1545_, v_a_1537_, v_a_1538_);
lean_dec(v_x_1545_);
return v___x_1554_;
}
}
else
{
lean_object* v___x_1555_; 
lean_dec(v_x_1536_);
v___x_1555_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1545_, v_a_1537_, v_a_1538_);
lean_dec(v_x_1545_);
return v___x_1555_;
}
}
else
{
lean_object* v___x_1556_; 
lean_dec(v_x_1536_);
v___x_1556_ = l_Lean_Syntax_isLit_x3f(v___x_1546_, v_x_1545_);
if (lean_obj_tag(v___x_1556_) == 1)
{
lean_object* v_val_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_x_1545_);
v_val_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_val_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
lean_ctor_set_tag(v___x_1559_, 0);
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_val_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v___x_1556_);
v___x_1565_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_1566_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1545_, v___x_1565_, v_a_1537_, v_a_1538_);
lean_dec(v_x_1545_);
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object* v_x_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lake_Toml_elabSimpleKey(v_x_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object* v_elabVal_1572_, size_t v_sz_1573_, size_t v_i_1574_, lean_object* v_bs_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_usize_dec_lt(v_i_1574_, v_sz_1573_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_dec_ref(v_elabVal_1572_);
v___x_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_bs_1575_);
return v___x_1580_;
}
else
{
lean_object* v_v_1581_; lean_object* v___x_1582_; 
v_v_1581_ = lean_array_uget_borrowed(v_bs_1575_, v_i_1574_);
lean_inc_ref(v_elabVal_1572_);
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v_v_1581_);
v___x_1582_ = lean_apply_4(v_elabVal_1572_, v_v_1581_, v___y_1576_, v___y_1577_, lean_box(0));
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; lean_object* v_bs_x27_1585_; size_t v___x_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = lean_unsigned_to_nat(0u);
v_bs_x27_1585_ = lean_array_uset(v_bs_1575_, v_i_1574_, v___x_1584_);
v___x_1586_ = ((size_t)1ULL);
v___x_1587_ = lean_usize_add(v_i_1574_, v___x_1586_);
v___x_1588_ = lean_array_uset(v_bs_x27_1585_, v_i_1574_, v_a_1583_);
v_i_1574_ = v___x_1587_;
v_bs_1575_ = v___x_1588_;
goto _start;
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_bs_1575_);
lean_dec_ref(v_elabVal_1572_);
v_a_1590_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1582_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1582_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object* v_elabVal_1598_, lean_object* v_sz_1599_, lean_object* v_i_1600_, lean_object* v_bs_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
size_t v_sz_boxed_1605_; size_t v_i_boxed_1606_; lean_object* v_res_1607_; 
v_sz_boxed_1605_ = lean_unbox_usize(v_sz_1599_);
lean_dec(v_sz_1599_);
v_i_boxed_1606_ = lean_unbox_usize(v_i_1600_);
lean_dec(v_i_1600_);
v_res_1607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1598_, v_sz_boxed_1605_, v_i_boxed_1606_, v_bs_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1607_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2));
v___x_1615_ = l_Lean_stringToMessageData(v___x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object* v_x_1616_, lean_object* v_elabVal_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_1616_);
v___x_1622_ = l_Lean_Syntax_isOfKind(v_x_1616_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_dec_ref(v_elabVal_1617_);
v___x_1623_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3);
v___x_1624_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1616_, v___x_1623_, v_a_1618_, v_a_1619_);
lean_dec(v_x_1616_);
return v___x_1624_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v_xs_1627_; lean_object* v___x_1628_; size_t v_sz_1629_; size_t v___x_1630_; lean_object* v___x_1631_; 
v___x_1625_ = lean_unsigned_to_nat(1u);
v___x_1626_ = l_Lean_Syntax_getArg(v_x_1616_, v___x_1625_);
lean_dec(v_x_1616_);
v_xs_1627_ = l_Lean_Syntax_getArgs(v___x_1626_);
lean_dec(v___x_1626_);
v___x_1628_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1627_);
lean_dec_ref(v_xs_1627_);
v_sz_1629_ = lean_array_size(v___x_1628_);
v___x_1630_ = ((size_t)0ULL);
v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1617_, v_sz_1629_, v___x_1630_, v___x_1628_, v_a_1618_, v_a_1619_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object* v_x_1632_, lean_object* v_elabVal_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1632_, v_elabVal_1633_, v_a_1634_, v_a_1635_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object* v_00_u03b1_1638_, lean_object* v_x_1639_, lean_object* v_elabVal_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1639_, v_elabVal_1640_, v_a_1641_, v_a_1642_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object* v_00_u03b1_1645_, lean_object* v_x_1646_, lean_object* v_elabVal_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(v_00_u03b1_1645_, v_x_1646_, v_elabVal_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object* v_00_u03b1_1652_, lean_object* v_elabVal_1653_, size_t v_sz_1654_, size_t v_i_1655_, lean_object* v_bs_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1653_, v_sz_1654_, v_i_1655_, v_bs_1656_, v___y_1657_, v___y_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object* v_00_u03b1_1661_, lean_object* v_elabVal_1662_, lean_object* v_sz_1663_, lean_object* v_i_1664_, lean_object* v_bs_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
size_t v_sz_boxed_1669_; size_t v_i_boxed_1670_; lean_object* v_res_1671_; 
v_sz_boxed_1669_ = lean_unbox_usize(v_sz_1663_);
lean_dec(v_sz_1663_);
v_i_boxed_1670_ = lean_unbox_usize(v_i_1664_);
lean_dec(v_i_1664_);
v_res_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(v_00_u03b1_1661_, v_elabVal_1662_, v_sz_boxed_1669_, v_i_boxed_1670_, v_bs_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(lean_object* v_msg_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_ref_1676_; lean_object* v___x_1677_; lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1686_; 
v_ref_1676_ = lean_ctor_get(v___y_1673_, 5);
v___x_1677_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_1672_, v___y_1673_, v___y_1674_);
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
lean_inc(v_ref_1676_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_ref_1676_);
lean_ctor_set(v___x_1682_, 1, v_a_1678_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set_tag(v___x_1680_, 1);
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(lean_object* v_ref_1692_, lean_object* v_msg_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_fileName_1698_; lean_object* v_fileMap_1699_; lean_object* v_options_1700_; lean_object* v_currRecDepth_1701_; lean_object* v_maxRecDepth_1702_; lean_object* v_ref_1703_; lean_object* v_currNamespace_1704_; lean_object* v_openDecls_1705_; lean_object* v_initHeartbeats_1706_; lean_object* v_maxHeartbeats_1707_; lean_object* v_quotContext_1708_; lean_object* v_currMacroScope_1709_; uint8_t v_diag_1710_; lean_object* v_cancelTk_x3f_1711_; uint8_t v_suppressElabErrors_1712_; lean_object* v_inheritedTraceOptions_1713_; lean_object* v_ref_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v_fileName_1698_ = lean_ctor_get(v___y_1695_, 0);
v_fileMap_1699_ = lean_ctor_get(v___y_1695_, 1);
v_options_1700_ = lean_ctor_get(v___y_1695_, 2);
v_currRecDepth_1701_ = lean_ctor_get(v___y_1695_, 3);
v_maxRecDepth_1702_ = lean_ctor_get(v___y_1695_, 4);
v_ref_1703_ = lean_ctor_get(v___y_1695_, 5);
v_currNamespace_1704_ = lean_ctor_get(v___y_1695_, 6);
v_openDecls_1705_ = lean_ctor_get(v___y_1695_, 7);
v_initHeartbeats_1706_ = lean_ctor_get(v___y_1695_, 8);
v_maxHeartbeats_1707_ = lean_ctor_get(v___y_1695_, 9);
v_quotContext_1708_ = lean_ctor_get(v___y_1695_, 10);
v_currMacroScope_1709_ = lean_ctor_get(v___y_1695_, 11);
v_diag_1710_ = lean_ctor_get_uint8(v___y_1695_, sizeof(void*)*14);
v_cancelTk_x3f_1711_ = lean_ctor_get(v___y_1695_, 12);
v_suppressElabErrors_1712_ = lean_ctor_get_uint8(v___y_1695_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1713_ = lean_ctor_get(v___y_1695_, 13);
v_ref_1714_ = l_Lean_replaceRef(v_ref_1692_, v_ref_1703_);
lean_inc_ref(v_inheritedTraceOptions_1713_);
lean_inc(v_cancelTk_x3f_1711_);
lean_inc(v_currMacroScope_1709_);
lean_inc(v_quotContext_1708_);
lean_inc(v_maxHeartbeats_1707_);
lean_inc(v_initHeartbeats_1706_);
lean_inc(v_openDecls_1705_);
lean_inc(v_currNamespace_1704_);
lean_inc(v_maxRecDepth_1702_);
lean_inc(v_currRecDepth_1701_);
lean_inc_ref(v_options_1700_);
lean_inc_ref(v_fileMap_1699_);
lean_inc_ref(v_fileName_1698_);
v___x_1715_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1715_, 0, v_fileName_1698_);
lean_ctor_set(v___x_1715_, 1, v_fileMap_1699_);
lean_ctor_set(v___x_1715_, 2, v_options_1700_);
lean_ctor_set(v___x_1715_, 3, v_currRecDepth_1701_);
lean_ctor_set(v___x_1715_, 4, v_maxRecDepth_1702_);
lean_ctor_set(v___x_1715_, 5, v_ref_1714_);
lean_ctor_set(v___x_1715_, 6, v_currNamespace_1704_);
lean_ctor_set(v___x_1715_, 7, v_openDecls_1705_);
lean_ctor_set(v___x_1715_, 8, v_initHeartbeats_1706_);
lean_ctor_set(v___x_1715_, 9, v_maxHeartbeats_1707_);
lean_ctor_set(v___x_1715_, 10, v_quotContext_1708_);
lean_ctor_set(v___x_1715_, 11, v_currMacroScope_1709_);
lean_ctor_set(v___x_1715_, 12, v_cancelTk_x3f_1711_);
lean_ctor_set(v___x_1715_, 13, v_inheritedTraceOptions_1713_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*14, v_diag_1710_);
lean_ctor_set_uint8(v___x_1715_, sizeof(void*)*14 + 1, v_suppressElabErrors_1712_);
v___x_1716_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_1693_, v___x_1715_, v___y_1696_);
lean_dec_ref(v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg___boxed(lean_object* v_ref_1717_, lean_object* v_msg_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v_ref_1717_, v_msg_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v_ref_1717_);
return v_res_1723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1));
v___x_1727_ = l_Lean_stringToMessageData(v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object* v_t_1728_, uint8_t v___x_1729_, lean_object* v_as_1730_, size_t v_i_1731_, size_t v_stop_1732_, lean_object* v_b_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_fst_1739_; lean_object* v_snd_1740_; uint8_t v___x_1744_; 
v___x_1744_ = lean_usize_dec_eq(v_i_1731_, v_stop_1732_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_array_uget_borrowed(v_as_1730_, v_i_1731_);
lean_inc(v___x_1745_);
v___x_1746_ = l_Lake_Toml_elabSimpleKey(v___x_1745_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1767_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1749_ = l_Lean_Name_str___override(v_b_1733_, v_a_1747_);
lean_inc_ref(v_t_1728_);
lean_inc(v___x_1749_);
v___x_1767_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1748_, v___x_1749_, v_t_1728_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_box(0);
lean_inc(v___x_1749_);
v___x_1769_ = l_Lake_Toml_RBDict_push___redArg(v___x_1748_, v___x_1749_, v___x_1768_, v___y_1734_);
v_fst_1739_ = v___x_1749_;
v_snd_1740_ = v___x_1769_;
goto v___jp_1738_;
}
else
{
lean_object* v_val_1770_; lean_object* v_snd_1771_; 
v_val_1770_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_val_1770_);
lean_dec_ref(v___x_1767_);
v_snd_1771_ = lean_ctor_get(v_val_1770_, 1);
lean_inc(v_snd_1771_);
lean_dec(v_val_1770_);
if (lean_obj_tag(v_snd_1771_) == 0)
{
if (v___x_1729_ == 0)
{
goto v___jp_1750_;
}
else
{
v_fst_1739_ = v___x_1749_;
v_snd_1740_ = v___y_1734_;
goto v___jp_1738_;
}
}
else
{
lean_dec_ref(v_snd_1771_);
goto v___jp_1750_;
}
}
v___jp_1750_:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1751_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
lean_inc(v___x_1749_);
v___x_1752_ = l_Lean_MessageData_ofName(v___x_1749_);
v___x_1753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1751_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1753_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
v___x_1756_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v___x_1745_, v___x_1755_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec_ref(v___y_1734_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v_snd_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v_snd_1758_ = lean_ctor_get(v_a_1757_, 1);
lean_inc(v_snd_1758_);
lean_dec(v_a_1757_);
v_fst_1739_ = v___x_1749_;
v_snd_1740_ = v_snd_1758_;
goto v___jp_1738_;
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v___x_1749_);
lean_dec_ref(v_t_1728_);
v_a_1759_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1756_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1756_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v___y_1734_);
lean_dec(v_b_1733_);
lean_dec_ref(v_t_1728_);
v_a_1772_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1746_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1746_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec_ref(v_t_1728_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v_b_1733_);
lean_ctor_set(v___x_1780_, 1, v___y_1734_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
v___jp_1738_:
{
size_t v___x_1741_; size_t v___x_1742_; 
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1731_, v___x_1741_);
v_i_1731_ = v___x_1742_;
v_b_1733_ = v_fst_1739_;
v___y_1734_ = v_snd_1740_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object* v_t_1782_, lean_object* v___x_1783_, lean_object* v_as_1784_, lean_object* v_i_1785_, lean_object* v_stop_1786_, lean_object* v_b_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
uint8_t v___x_9533__boxed_1792_; size_t v_i_boxed_1793_; size_t v_stop_boxed_1794_; lean_object* v_res_1795_; 
v___x_9533__boxed_1792_ = lean_unbox(v___x_1783_);
v_i_boxed_1793_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_stop_boxed_1794_ = lean_unbox_usize(v_stop_1786_);
lean_dec(v_stop_1786_);
v_res_1795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_t_1782_, v___x_9533__boxed_1792_, v_as_1784_, v_i_boxed_1793_, v_stop_boxed_1794_, v_b_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec_ref(v_as_1784_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(size_t v_sz_1796_, size_t v_i_1797_, lean_object* v_bs_1798_){
_start:
{
uint8_t v___x_1799_; 
v___x_1799_ = lean_usize_dec_lt(v_i_1797_, v_sz_1796_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1800_, 0, v_bs_1798_);
return v___x_1800_;
}
else
{
lean_object* v_v_1801_; lean_object* v___x_1802_; lean_object* v_bs_x27_1803_; size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v_v_1801_ = lean_array_uget(v_bs_1798_, v_i_1797_);
v___x_1802_ = lean_unsigned_to_nat(0u);
v_bs_x27_1803_ = lean_array_uset(v_bs_1798_, v_i_1797_, v___x_1802_);
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_i_1797_, v___x_1804_);
v___x_1806_ = lean_array_uset(v_bs_x27_1803_, v_i_1797_, v_v_1801_);
v_i_1797_ = v___x_1805_;
v_bs_1798_ = v___x_1806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object* v_sz_1808_, lean_object* v_i_1809_, lean_object* v_bs_1810_){
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1808_);
lean_dec(v_sz_1808_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1809_);
lean_dec(v_i_1809_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_sz_boxed_1811_, v_i_boxed_1812_, v_bs_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t v___x_1814_, lean_object* v_as_1815_, size_t v_i_1816_, size_t v_stop_1817_, lean_object* v_b_1818_){
_start:
{
lean_object* v___y_1820_; uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_eq(v_i_1816_, v_stop_1817_);
if (v___x_1824_ == 0)
{
lean_object* v_fst_1825_; uint8_t v___x_1826_; 
v_fst_1825_ = lean_ctor_get(v_b_1818_, 0);
v___x_1826_ = lean_unbox(v_fst_1825_);
if (v___x_1826_ == 0)
{
lean_object* v_snd_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1835_; 
v_snd_1827_ = lean_ctor_get(v_b_1818_, 1);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_b_1818_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v_b_1818_, 0);
lean_dec(v_unused_1836_);
v___x_1829_ = v_b_1818_;
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_snd_1827_);
lean_dec(v_b_1818_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1835_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_box(v___x_1814_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_snd_1827_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
v___y_1820_ = v___x_1833_;
goto v___jp_1819_;
}
}
}
else
{
lean_object* v_snd_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1847_; 
v_snd_1837_ = lean_ctor_get(v_b_1818_, 1);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_b_1818_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v_b_1818_, 0);
lean_dec(v_unused_1848_);
v___x_1839_ = v_b_1818_;
v_isShared_1840_ = v_isSharedCheck_1847_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_snd_1837_);
lean_dec(v_b_1818_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1847_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1841_ = lean_array_uget_borrowed(v_as_1815_, v_i_1816_);
lean_inc(v___x_1841_);
v___x_1842_ = lean_array_push(v_snd_1837_, v___x_1841_);
v___x_1843_ = lean_box(v___x_1824_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___x_1842_);
lean_ctor_set(v___x_1839_, 0, v___x_1843_);
v___x_1845_ = v___x_1839_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1842_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
v___y_1820_ = v___x_1845_;
goto v___jp_1819_;
}
}
}
}
else
{
return v_b_1818_;
}
v___jp_1819_:
{
size_t v___x_1821_; size_t v___x_1822_; 
v___x_1821_ = ((size_t)1ULL);
v___x_1822_ = lean_usize_add(v_i_1816_, v___x_1821_);
v_i_1816_ = v___x_1822_;
v_b_1818_ = v___y_1820_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object* v___x_1849_, lean_object* v_as_1850_, lean_object* v_i_1851_, lean_object* v_stop_1852_, lean_object* v_b_1853_){
_start:
{
uint8_t v___x_9654__boxed_1854_; size_t v_i_boxed_1855_; size_t v_stop_boxed_1856_; lean_object* v_res_1857_; 
v___x_9654__boxed_1854_ = lean_unbox(v___x_1849_);
v_i_boxed_1855_ = lean_unbox_usize(v_i_1851_);
lean_dec(v_i_1851_);
v_stop_boxed_1856_ = lean_unbox_usize(v_stop_1852_);
lean_dec(v_stop_1852_);
v_res_1857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_9654__boxed_1854_, v_as_1850_, v_i_boxed_1855_, v_stop_boxed_1856_, v_b_1853_);
lean_dec_ref(v_as_1850_);
return v_res_1857_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2));
v___x_1865_ = l_Lean_stringToMessageData(v___x_1864_);
return v___x_1865_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6));
v___x_1873_ = l_Lean_stringToMessageData(v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object* v_elabVal_1876_, lean_object* v_as_1877_, size_t v_i_1878_, size_t v_stop_1879_, lean_object* v_b_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_a_1885_; lean_object* v___y_1890_; uint8_t v___x_1892_; 
v___x_1892_ = lean_usize_dec_eq(v_i_1878_, v_stop_1879_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1));
v___x_1894_ = lean_array_uget_borrowed(v_as_1877_, v_i_1878_);
lean_inc(v___x_1894_);
v___x_1895_ = l_Lean_Syntax_isOfKind(v___x_1894_, v___x_1893_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec_ref(v_b_1880_);
v___x_1896_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3);
v___x_1897_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1894_, v___x_1896_, v___y_1881_, v___y_1882_);
v___y_1890_ = v___x_1897_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = l_Lean_Syntax_getArg(v___x_1894_, v___x_1898_);
v___x_1900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5));
lean_inc(v___x_1899_);
v___x_1901_ = l_Lean_Syntax_isOfKind(v___x_1899_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec_ref(v_b_1880_);
v___x_1902_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1903_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1899_, v___x_1902_, v___y_1881_, v___y_1882_);
lean_dec(v___x_1899_);
v___y_1890_ = v___x_1903_;
goto v___jp_1889_;
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v_v_1906_; lean_object* v___y_1908_; lean_object* v_fst_1909_; lean_object* v_snd_1910_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1956_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1904_ = lean_unsigned_to_nat(2u);
v___x_1905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v_v_1906_ = l_Lean_Syntax_getArg(v___x_1894_, v___x_1904_);
v___x_1977_ = l_Lean_Syntax_getArg(v___x_1899_, v___x_1898_);
v___x_1978_ = l_Lean_Syntax_getArgs(v___x_1977_);
lean_dec(v___x_1977_);
v___x_1979_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8));
v___x_1980_ = lean_array_get_size(v___x_1978_);
v___x_1981_ = lean_nat_dec_lt(v___x_1898_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_dec_ref(v___x_1978_);
v___y_1956_ = v___x_1979_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1982_ = lean_box(v___x_1901_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1979_);
v___x_1984_ = lean_nat_dec_le(v___x_1980_, v___x_1980_);
if (v___x_1984_ == 0)
{
if (v___x_1981_ == 0)
{
lean_dec_ref(v___x_1983_);
lean_dec_ref(v___x_1978_);
v___y_1956_ = v___x_1979_;
goto v___jp_1955_;
}
else
{
size_t v___x_1985_; size_t v___x_1986_; lean_object* v___x_1987_; lean_object* v_snd_1988_; 
v___x_1985_ = ((size_t)0ULL);
v___x_1986_ = lean_usize_of_nat(v___x_1980_);
v___x_1987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1901_, v___x_1978_, v___x_1985_, v___x_1986_, v___x_1983_);
lean_dec_ref(v___x_1978_);
v_snd_1988_ = lean_ctor_get(v___x_1987_, 1);
lean_inc(v_snd_1988_);
lean_dec_ref(v___x_1987_);
v___y_1956_ = v_snd_1988_;
goto v___jp_1955_;
}
}
else
{
size_t v___x_1989_; size_t v___x_1990_; lean_object* v___x_1991_; lean_object* v_snd_1992_; 
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = lean_usize_of_nat(v___x_1980_);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1901_, v___x_1978_, v___x_1989_, v___x_1990_, v___x_1983_);
lean_dec_ref(v___x_1978_);
v_snd_1992_ = lean_ctor_get(v___x_1991_, 1);
lean_inc(v_snd_1992_);
lean_dec_ref(v___x_1991_);
v___y_1956_ = v_snd_1992_;
goto v___jp_1955_;
}
}
v___jp_1907_:
{
lean_object* v___x_1911_; 
lean_inc(v___y_1908_);
v___x_1911_ = l_Lake_Toml_elabSimpleKey(v___y_1908_, v___y_1881_, v___y_1882_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = l_Lean_Name_str___override(v_fst_1909_, v_a_1912_);
lean_inc_ref(v_snd_1910_);
lean_inc(v___x_1913_);
v___x_1914_ = l_Lake_Toml_RBDict_contains___redArg(v___x_1905_, v___x_1913_, v_snd_1910_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec(v___y_1908_);
lean_inc_ref(v_elabVal_1876_);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
v___x_1915_ = lean_apply_4(v_elabVal_1876_, v_v_1906_, v___y_1881_, v___y_1882_, lean_box(0));
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_a_1916_);
v___x_1918_ = l_Lake_Toml_RBDict_push___redArg(v___x_1905_, v___x_1913_, v___x_1917_, v_snd_1910_);
v_a_1885_ = v___x_1918_;
goto v___jp_1884_;
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v___x_1913_);
lean_dec_ref(v_snd_1910_);
lean_dec_ref(v_elabVal_1876_);
v_a_1919_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1915_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1915_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
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
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec_ref(v_snd_1910_);
lean_dec(v_v_1906_);
v___x_1927_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
v___x_1928_ = l_Lean_MessageData_ofName(v___x_1913_);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___y_1908_, v___x_1931_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1908_);
v___y_1890_ = v___x_1932_;
goto v___jp_1889_;
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec_ref(v_snd_1910_);
lean_dec(v_fst_1909_);
lean_dec(v___y_1908_);
lean_dec(v_v_1906_);
lean_dec_ref(v_elabVal_1876_);
v_a_1933_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1911_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1911_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
v___jp_1941_:
{
if (lean_obj_tag(v___y_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v_fst_1945_; lean_object* v_snd_1946_; 
v_a_1944_ = lean_ctor_get(v___y_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___y_1943_);
v_fst_1945_ = lean_ctor_get(v_a_1944_, 0);
lean_inc(v_fst_1945_);
v_snd_1946_ = lean_ctor_get(v_a_1944_, 1);
lean_inc(v_snd_1946_);
lean_dec(v_a_1944_);
v___y_1908_ = v___y_1942_;
v_fst_1909_ = v_fst_1945_;
v_snd_1910_ = v_snd_1946_;
goto v___jp_1907_;
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v___y_1942_);
lean_dec(v_v_1906_);
lean_dec_ref(v_elabVal_1876_);
v_a_1947_ = lean_ctor_get(v___y_1943_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___y_1943_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___y_1943_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___y_1943_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
v___jp_1955_:
{
size_t v_sz_1957_; size_t v___x_1958_; lean_object* v___x_1959_; 
v_sz_1957_ = lean_array_size(v___y_1956_);
v___x_1958_ = ((size_t)0ULL);
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_sz_1957_, v___x_1958_, v___y_1956_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec(v_v_1906_);
lean_dec_ref(v_b_1880_);
v___x_1960_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1961_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1899_, v___x_1960_, v___y_1881_, v___y_1882_);
lean_dec(v___x_1899_);
v___y_1890_ = v___x_1961_;
goto v___jp_1889_;
}
else
{
lean_object* v_val_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v_tailKey_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
lean_dec(v___x_1899_);
v_val_1962_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_val_1962_);
lean_dec_ref(v___x_1959_);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_array_get_size(v_val_1962_);
v___x_1965_ = lean_unsigned_to_nat(1u);
v___x_1966_ = lean_nat_sub(v___x_1964_, v___x_1965_);
v_tailKey_1967_ = lean_array_get(v___x_1963_, v_val_1962_, v___x_1966_);
lean_dec(v___x_1966_);
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_array_pop(v_val_1962_);
v___x_1970_ = lean_array_get_size(v___x_1969_);
v___x_1971_ = lean_nat_dec_lt(v___x_1898_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_dec_ref(v___x_1969_);
v___y_1908_ = v_tailKey_1967_;
v_fst_1909_ = v___x_1968_;
v_snd_1910_ = v_b_1880_;
goto v___jp_1907_;
}
else
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_nat_dec_le(v___x_1970_, v___x_1970_);
if (v___x_1972_ == 0)
{
if (v___x_1971_ == 0)
{
lean_dec_ref(v___x_1969_);
v___y_1908_ = v_tailKey_1967_;
v_fst_1909_ = v___x_1968_;
v_snd_1910_ = v_b_1880_;
goto v___jp_1907_;
}
else
{
size_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = lean_usize_of_nat(v___x_1970_);
lean_inc_ref(v_b_1880_);
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1880_, v___x_1901_, v___x_1969_, v___x_1958_, v___x_1973_, v___x_1968_, v_b_1880_, v___y_1881_, v___y_1882_);
lean_dec_ref(v___x_1969_);
v___y_1942_ = v_tailKey_1967_;
v___y_1943_ = v___x_1974_;
goto v___jp_1941_;
}
}
else
{
size_t v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_usize_of_nat(v___x_1970_);
lean_inc_ref(v_b_1880_);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1880_, v___x_1901_, v___x_1969_, v___x_1958_, v___x_1975_, v___x_1968_, v_b_1880_, v___y_1881_, v___y_1882_);
lean_dec_ref(v___x_1969_);
v___y_1942_ = v_tailKey_1967_;
v___y_1943_ = v___x_1976_;
goto v___jp_1941_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1993_; 
lean_dec_ref(v_elabVal_1876_);
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_b_1880_);
return v___x_1993_;
}
v___jp_1884_:
{
size_t v___x_1886_; size_t v___x_1887_; 
v___x_1886_ = ((size_t)1ULL);
v___x_1887_ = lean_usize_add(v_i_1878_, v___x_1886_);
v_i_1878_ = v___x_1887_;
v_b_1880_ = v_a_1885_;
goto _start;
}
v___jp_1889_:
{
if (lean_obj_tag(v___y_1890_) == 0)
{
lean_object* v_a_1891_; 
v_a_1891_ = lean_ctor_get(v___y_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref(v___y_1890_);
v_a_1885_ = v_a_1891_;
goto v___jp_1884_;
}
else
{
lean_dec_ref(v_elabVal_1876_);
return v___y_1890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object* v_elabVal_1994_, lean_object* v_as_1995_, lean_object* v_i_1996_, lean_object* v_stop_1997_, lean_object* v_b_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
size_t v_i_boxed_2002_; size_t v_stop_boxed_2003_; lean_object* v_res_2004_; 
v_i_boxed_2002_ = lean_unbox_usize(v_i_1996_);
lean_dec(v_i_1996_);
v_stop_boxed_2003_ = lean_unbox_usize(v_stop_1997_);
lean_dec(v_stop_1997_);
v_res_2004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1994_, v_as_1995_, v_i_boxed_2002_, v_stop_boxed_2003_, v_b_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec_ref(v_as_1995_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object* v_as_2005_, size_t v_i_2006_, size_t v_stop_2007_, lean_object* v_b_2008_){
_start:
{
lean_object* v___y_2010_; uint8_t v___x_2014_; 
v___x_2014_ = lean_usize_dec_eq(v_i_2006_, v_stop_2007_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v_snd_2016_; 
v___x_2015_ = lean_array_uget_borrowed(v_as_2005_, v_i_2006_);
v_snd_2016_ = lean_ctor_get(v___x_2015_, 1);
if (lean_obj_tag(v_snd_2016_) == 1)
{
lean_object* v_fst_2017_; lean_object* v_val_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_fst_2017_ = lean_ctor_get(v___x_2015_, 0);
v_val_2018_ = lean_ctor_get(v_snd_2016_, 0);
v___x_2019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
lean_inc(v_val_2018_);
lean_inc(v_fst_2017_);
v___x_2020_ = l_Lake_Toml_RBDict_push___redArg(v___x_2019_, v_fst_2017_, v_val_2018_, v_b_2008_);
v___y_2010_ = v___x_2020_;
goto v___jp_2009_;
}
else
{
v___y_2010_ = v_b_2008_;
goto v___jp_2009_;
}
}
else
{
return v_b_2008_;
}
v___jp_2009_:
{
size_t v___x_2011_; size_t v___x_2012_; 
v___x_2011_ = ((size_t)1ULL);
v___x_2012_ = lean_usize_add(v_i_2006_, v___x_2011_);
v_i_2006_ = v___x_2012_;
v_b_2008_ = v___y_2010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object* v_as_2021_, lean_object* v_i_2022_, lean_object* v_stop_2023_, lean_object* v_b_2024_){
_start:
{
size_t v_i_boxed_2025_; size_t v_stop_boxed_2026_; lean_object* v_res_2027_; 
v_i_boxed_2025_ = lean_unbox_usize(v_i_2022_);
lean_dec(v_i_2022_);
v_stop_boxed_2026_ = lean_unbox_usize(v_stop_2023_);
lean_dec(v_stop_2023_);
v_res_2027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_as_2021_, v_i_boxed_2025_, v_stop_boxed_2026_, v_b_2024_);
lean_dec_ref(v_as_2021_);
return v_res_2027_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2));
v___x_2035_ = l_Lean_stringToMessageData(v___x_2034_);
return v___x_2035_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_2037_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_2036_);
return v___x_2037_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5(void){
_start:
{
lean_object* v___x_2038_; lean_object* v_t_2039_; 
v___x_2038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v_t_2039_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_2038_);
return v_t_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object* v_x_2040_, lean_object* v_elabVal_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2040_);
v___x_2046_ = l_Lean_Syntax_isOfKind(v_x_2040_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v_elabVal_2041_);
v___x_2047_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3);
v___x_2048_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2040_, v___x_2047_, v_a_2042_, v_a_2043_);
lean_dec(v_x_2040_);
return v___x_2048_;
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v_kvs_2052_; lean_object* v_a_2054_; lean_object* v___y_2071_; lean_object* v_t_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2049_ = lean_unsigned_to_nat(0u);
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = l_Lean_Syntax_getArg(v_x_2040_, v___x_2050_);
lean_dec(v_x_2040_);
v_kvs_2052_ = l_Lean_Syntax_getArgs(v___x_2051_);
lean_dec(v___x_2051_);
v_t_2081_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5);
v___x_2082_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_kvs_2052_);
lean_dec_ref(v_kvs_2052_);
v___x_2083_ = lean_array_get_size(v___x_2082_);
v___x_2084_ = lean_nat_dec_lt(v___x_2049_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v___x_2082_);
lean_dec_ref(v_elabVal_2041_);
v_a_2054_ = v_t_2081_;
goto v___jp_2053_;
}
else
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_nat_dec_le(v___x_2083_, v___x_2083_);
if (v___x_2085_ == 0)
{
if (v___x_2084_ == 0)
{
lean_dec_ref(v___x_2082_);
lean_dec_ref(v_elabVal_2041_);
v_a_2054_ = v_t_2081_;
goto v___jp_2053_;
}
else
{
size_t v___x_2086_; size_t v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = ((size_t)0ULL);
v___x_2087_ = lean_usize_of_nat(v___x_2083_);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_2041_, v___x_2082_, v___x_2086_, v___x_2087_, v_t_2081_, v_a_2042_, v_a_2043_);
lean_dec_ref(v___x_2082_);
v___y_2071_ = v___x_2088_;
goto v___jp_2070_;
}
}
else
{
size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = ((size_t)0ULL);
v___x_2090_ = lean_usize_of_nat(v___x_2083_);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_2041_, v___x_2082_, v___x_2089_, v___x_2090_, v_t_2081_, v_a_2042_, v_a_2043_);
lean_dec_ref(v___x_2082_);
v___y_2071_ = v___x_2091_;
goto v___jp_2070_;
}
}
v___jp_2053_:
{
lean_object* v_items_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_items_2055_ = lean_ctor_get(v_a_2054_, 0);
lean_inc_ref(v_items_2055_);
lean_dec_ref(v_a_2054_);
v___x_2056_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
v___x_2057_ = lean_array_get_size(v_items_2055_);
v___x_2058_ = lean_nat_dec_lt(v___x_2049_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; 
lean_dec_ref(v_items_2055_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2056_);
return v___x_2059_;
}
else
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_nat_dec_le(v___x_2057_, v___x_2057_);
if (v___x_2060_ == 0)
{
if (v___x_2058_ == 0)
{
lean_object* v___x_2061_; 
lean_dec_ref(v_items_2055_);
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2056_);
return v___x_2061_;
}
else
{
size_t v___x_2062_; size_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2062_ = ((size_t)0ULL);
v___x_2063_ = lean_usize_of_nat(v___x_2057_);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_2055_, v___x_2062_, v___x_2063_, v___x_2056_);
lean_dec_ref(v_items_2055_);
v___x_2065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
return v___x_2065_;
}
}
else
{
size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = ((size_t)0ULL);
v___x_2067_ = lean_usize_of_nat(v___x_2057_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_2055_, v___x_2066_, v___x_2067_, v___x_2056_);
lean_dec_ref(v_items_2055_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
}
v___jp_2070_:
{
if (lean_obj_tag(v___y_2071_) == 0)
{
lean_object* v_a_2072_; 
v_a_2072_ = lean_ctor_get(v___y_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___y_2071_);
v_a_2054_ = v_a_2072_;
goto v___jp_2053_;
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
v_a_2073_ = lean_ctor_get(v___y_2071_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___y_2071_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___y_2071_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___y_2071_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object* v_x_2092_, lean_object* v_elabVal_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2092_, v_elabVal_2093_, v_a_2094_, v_a_2095_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(lean_object* v_00_u03b1_2098_, lean_object* v_ref_2099_, lean_object* v_msg_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v_ref_2099_, v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_ref_2107_, lean_object* v_msg_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_00_u03b1_2106_, v_ref_2107_, v_msg_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v_ref_2107_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(lean_object* v_00_u03b1_2114_, lean_object* v_msg_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_2115_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2121_, lean_object* v_msg_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(v_00_u03b1_2121_, v_msg_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2127_;
}
}
static lean_object* _init_l_Lake_Toml_elabVal___closed__1(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = ((lean_object*)(l_Lake_Toml_elabVal___closed__0));
v___x_2130_ = l_Lean_stringToMessageData(v___x_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object* v_x_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lake_Toml_elabVal(v_x_2131_, v_a_2132_, v_a_2133_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object* v_x_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
lean_inc(v_x_2136_);
v___x_2141_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
lean_inc(v_x_2136_);
v___x_2143_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
lean_inc(v_x_2136_);
v___x_2145_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
lean_inc(v_x_2136_);
v___x_2147_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
lean_inc(v_x_2136_);
v___x_2149_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; uint8_t v___x_2151_; 
v___x_2150_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
lean_inc(v_x_2136_);
v___x_2151_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2150_);
if (v___x_2151_ == 0)
{
lean_object* v___x_2152_; uint8_t v___x_2153_; 
v___x_2152_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_2136_);
v___x_2153_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2152_);
if (v___x_2153_ == 0)
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_2136_);
v___x_2155_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
v___x_2156_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_2136_);
v___x_2157_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2156_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2158_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2136_);
v___x_2159_ = l_Lean_Syntax_isOfKind(v_x_2136_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = lean_obj_once(&l_Lake_Toml_elabVal___closed__1, &l_Lake_Toml_elabVal___closed__1_once, _init_l_Lake_Toml_elabVal___closed__1);
v___x_2161_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2136_, v___x_2160_, v_a_2137_, v_a_2138_);
lean_dec(v_x_2136_);
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2136_);
v___x_2163_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2136_, v___x_2162_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2172_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2172_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_x_2136_);
lean_ctor_set(v___x_2168_, 1, v_a_2164_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2168_);
v___x_2170_ = v___x_2166_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_x_2136_);
v_a_2173_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2163_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2163_);
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
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2136_);
v___x_2182_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_2136_, v___x_2181_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2191_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2185_ = v___x_2182_;
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2182_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2191_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2187_, 0, v_x_2136_);
lean_ctor_set(v___x_2187_, 1, v_a_2183_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2187_);
v___x_2189_ = v___x_2185_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_x_2136_);
v_a_2192_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2182_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2182_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_object* v___x_2200_; 
lean_inc(v_x_2136_);
v___x_2200_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2210_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; uint8_t v___x_2206_; lean_object* v___x_2208_; 
v___x_2205_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_2205_, 0, v_x_2136_);
v___x_2206_ = lean_unbox(v_a_2201_);
lean_dec(v_a_2201_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*1, v___x_2206_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2205_);
v___x_2208_ = v___x_2203_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2205_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_x_2136_);
v_a_2211_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2200_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2200_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
else
{
lean_object* v___x_2219_; 
lean_inc(v_x_2136_);
v___x_2219_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2228_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2224_, 0, v_x_2136_);
lean_ctor_set(v___x_2224_, 1, v_a_2220_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_dec(v_x_2136_);
v_a_2229_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2219_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2219_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
else
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2246_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2240_ = v___x_2237_;
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_x_2136_);
lean_ctor_set(v___x_2242_, 1, v_a_2238_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2242_);
v___x_2244_ = v___x_2240_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_x_2136_);
v_a_2247_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2237_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2237_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
else
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2265_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2258_ = v___x_2255_;
v_isShared_2259_ = v_isSharedCheck_2265_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2265_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2260_ = lean_nat_to_int(v_a_2256_);
v___x_2261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2261_, 0, v_x_2136_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 0, v___x_2261_);
v___x_2263_ = v___x_2258_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_x_2136_);
v_a_2266_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2255_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2255_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
else
{
lean_object* v___x_2274_; 
v___x_2274_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2284_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2284_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2284_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2279_ = lean_nat_to_int(v_a_2275_);
v___x_2280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2280_, 0, v_x_2136_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2280_);
v___x_2282_ = v___x_2277_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_x_2136_);
v_a_2285_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2274_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2274_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
else
{
lean_object* v___x_2293_; 
v___x_2293_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2303_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2303_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2303_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2301_; 
v___x_2298_ = lean_nat_to_int(v_a_2294_);
v___x_2299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2299_, 0, v_x_2136_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2299_);
v___x_2301_ = v___x_2296_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v_x_2136_);
v_a_2304_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2293_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2293_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
else
{
lean_object* v___x_2312_; 
v___x_2312_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2321_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_x_2136_);
lean_ctor_set(v___x_2317_, 1, v_a_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_x_2136_);
v_a_2322_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2312_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2312_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
else
{
lean_object* v___x_2330_; 
v___x_2330_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_2136_, v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2340_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2340_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2340_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; double v___x_2336_; lean_object* v___x_2338_; 
v___x_2335_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_2335_, 0, v_x_2136_);
v___x_2336_ = lean_unbox_float(v_a_2331_);
lean_dec(v_a_2331_);
lean_ctor_set_float(v___x_2335_, sizeof(void*)*1, v___x_2336_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2335_);
v___x_2338_ = v___x_2333_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2335_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_x_2136_);
v_a_2341_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2330_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2330_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Elab_Value(builtin);
}
#ifdef __cplusplus
}
#endif
