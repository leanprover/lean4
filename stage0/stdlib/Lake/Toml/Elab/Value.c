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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_substring_tostring(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cannot redefine key `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_14_; lean_object* v_toApplicative_15_; lean_object* v_toFunctor_16_; lean_object* v_toSeq_17_; lean_object* v_toSeqLeft_18_; lean_object* v_toSeqRight_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_14_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_15_ = lean_ctor_get(v___x_14_, 0);
v_toFunctor_16_ = lean_ctor_get(v_toApplicative_15_, 0);
v_toSeq_17_ = lean_ctor_get(v_toApplicative_15_, 2);
v_toSeqLeft_18_ = lean_ctor_get(v_toApplicative_15_, 3);
v_toSeqRight_19_ = lean_ctor_get(v_toApplicative_15_, 4);
v___f_20_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_21_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref_n(v_toFunctor_16_, 2);
v___f_22_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_22_, 0, v_toFunctor_16_);
v___f_23_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_23_, 0, v_toFunctor_16_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___f_22_);
lean_ctor_set(v___x_24_, 1, v___f_23_);
lean_inc(v_toSeqRight_19_);
v___f_25_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_25_, 0, v_toSeqRight_19_);
lean_inc(v_toSeqLeft_18_);
v___f_26_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_26_, 0, v_toSeqLeft_18_);
lean_inc(v_toSeq_17_);
v___f_27_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_27_, 0, v_toSeq_17_);
v___x_28_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_28_, 0, v___x_24_);
lean_ctor_set(v___x_28_, 1, v___f_20_);
lean_ctor_set(v___x_28_, 2, v___f_27_);
lean_ctor_set(v___x_28_, 3, v___f_26_);
lean_ctor_set(v___x_28_, 4, v___f_25_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___f_21_);
v___x_30_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_31_ = l_Lean_Core_instMonadRefCoreM;
v___x_32_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_29_);
v___x_33_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_32_, v___x_29_);
v___x_34_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_34_, 0, v___x_30_);
lean_ctor_set(v___x_34_, 1, v___x_31_);
lean_ctor_set(v___x_34_, 2, v___x_33_);
v___x_35_ = l_Lean_Syntax_isLit_x3f(v_k_8_, v_x_9_);
if (lean_obj_tag(v___x_35_) == 1)
{
lean_object* v_val_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_dec_ref_known(v___x_34_, 3);
lean_dec_ref_known(v___x_29_, 2);
lean_dec(v_x_9_);
v_val_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_val_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 0);
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_val_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_224__overap_50_; lean_object* v___x_51_; 
lean_dec(v___x_35_);
v___x_44_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4));
v___x_45_ = lean_string_append(v___x_44_, v_name_10_);
v___x_46_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5));
v___x_47_ = lean_string_append(v___x_45_, v___x_46_);
v___x_48_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
v___x_49_ = l_Lean_MessageData_ofFormat(v___x_48_);
v___x_224__overap_50_ = l_Lean_throwErrorAt___redArg(v___x_29_, v___x_34_, v_x_9_, v___x_49_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
v___x_51_ = lean_apply_3(v___x_224__overap_50_, v_a_11_, v_a_12_, lean_box(0));
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(lean_object* v_k_52_, lean_object* v_x_53_, lean_object* v_name_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(v_k_52_, v_x_53_, v_name_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec_ref(v_name_54_);
lean_dec(v_k_52_);
return v_res_58_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_59_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
lean_ctor_set(v___x_64_, 2, v___x_63_);
lean_ctor_set(v___x_64_, 3, v___x_63_);
lean_ctor_set(v___x_64_, 4, v___x_62_);
lean_ctor_set(v___x_64_, 5, v___x_62_);
lean_ctor_set(v___x_64_, 6, v___x_62_);
lean_ctor_set(v___x_64_, 7, v___x_62_);
lean_ctor_set(v___x_64_, 8, v___x_62_);
lean_ctor_set(v___x_64_, 9, v___x_62_);
lean_ctor_set(v___x_64_, 10, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_unsigned_to_nat(32u);
v___x_66_ = lean_mk_empty_array_with_capacity(v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_68_ = ((size_t)5ULL);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_unsigned_to_nat(32u);
v___x_71_ = lean_mk_empty_array_with_capacity(v___x_70_);
v___x_72_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3);
v___x_73_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_69_);
lean_ctor_set(v___x_73_, 3, v___x_69_);
lean_ctor_set_usize(v___x_73_, 4, v___x_68_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = lean_box(1);
v___x_75_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4);
v___x_76_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
v___x_77_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
lean_ctor_set(v___x_77_, 2, v___x_74_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(lean_object* v_msgData_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_env_83_; lean_object* v_options_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_env_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_83_);
lean_dec(v___x_82_);
v_options_84_ = lean_ctor_get(v___y_79_, 2);
v___x_85_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2);
v___x_86_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_84_);
v___x_87_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_87_, 0, v_env_83_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_86_);
lean_ctor_set(v___x_87_, 3, v_options_84_);
v___x_88_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_msgData_78_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msgData_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object* v_msg_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_ref_99_; lean_object* v___x_100_; lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_109_; 
v_ref_99_ = lean_ctor_get(v___y_96_, 5);
v___x_100_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_95_, v___y_96_, v___y_97_);
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_109_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_107_; 
lean_inc(v_ref_99_);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v_ref_99_);
lean_ctor_set(v___x_105_, 1, v_a_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set_tag(v___x_103_, 1);
lean_ctor_set(v___x_103_, 0, v___x_105_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object* v_ref_115_, lean_object* v_msg_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_fileName_120_; lean_object* v_fileMap_121_; lean_object* v_options_122_; lean_object* v_currRecDepth_123_; lean_object* v_maxRecDepth_124_; lean_object* v_ref_125_; lean_object* v_currNamespace_126_; lean_object* v_openDecls_127_; lean_object* v_initHeartbeats_128_; lean_object* v_maxHeartbeats_129_; lean_object* v_quotContext_130_; lean_object* v_currMacroScope_131_; uint8_t v_diag_132_; lean_object* v_cancelTk_x3f_133_; uint8_t v_suppressElabErrors_134_; lean_object* v_inheritedTraceOptions_135_; lean_object* v_ref_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_fileName_120_ = lean_ctor_get(v___y_117_, 0);
v_fileMap_121_ = lean_ctor_get(v___y_117_, 1);
v_options_122_ = lean_ctor_get(v___y_117_, 2);
v_currRecDepth_123_ = lean_ctor_get(v___y_117_, 3);
v_maxRecDepth_124_ = lean_ctor_get(v___y_117_, 4);
v_ref_125_ = lean_ctor_get(v___y_117_, 5);
v_currNamespace_126_ = lean_ctor_get(v___y_117_, 6);
v_openDecls_127_ = lean_ctor_get(v___y_117_, 7);
v_initHeartbeats_128_ = lean_ctor_get(v___y_117_, 8);
v_maxHeartbeats_129_ = lean_ctor_get(v___y_117_, 9);
v_quotContext_130_ = lean_ctor_get(v___y_117_, 10);
v_currMacroScope_131_ = lean_ctor_get(v___y_117_, 11);
v_diag_132_ = lean_ctor_get_uint8(v___y_117_, sizeof(void*)*14);
v_cancelTk_x3f_133_ = lean_ctor_get(v___y_117_, 12);
v_suppressElabErrors_134_ = lean_ctor_get_uint8(v___y_117_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_135_ = lean_ctor_get(v___y_117_, 13);
v_ref_136_ = l_Lean_replaceRef(v_ref_115_, v_ref_125_);
lean_inc_ref(v_inheritedTraceOptions_135_);
lean_inc(v_cancelTk_x3f_133_);
lean_inc(v_currMacroScope_131_);
lean_inc(v_quotContext_130_);
lean_inc(v_maxHeartbeats_129_);
lean_inc(v_initHeartbeats_128_);
lean_inc(v_openDecls_127_);
lean_inc(v_currNamespace_126_);
lean_inc(v_maxRecDepth_124_);
lean_inc(v_currRecDepth_123_);
lean_inc_ref(v_options_122_);
lean_inc_ref(v_fileMap_121_);
lean_inc_ref(v_fileName_120_);
v___x_137_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_137_, 0, v_fileName_120_);
lean_ctor_set(v___x_137_, 1, v_fileMap_121_);
lean_ctor_set(v___x_137_, 2, v_options_122_);
lean_ctor_set(v___x_137_, 3, v_currRecDepth_123_);
lean_ctor_set(v___x_137_, 4, v_maxRecDepth_124_);
lean_ctor_set(v___x_137_, 5, v_ref_136_);
lean_ctor_set(v___x_137_, 6, v_currNamespace_126_);
lean_ctor_set(v___x_137_, 7, v_openDecls_127_);
lean_ctor_set(v___x_137_, 8, v_initHeartbeats_128_);
lean_ctor_set(v___x_137_, 9, v_maxHeartbeats_129_);
lean_ctor_set(v___x_137_, 10, v_quotContext_130_);
lean_ctor_set(v___x_137_, 11, v_currMacroScope_131_);
lean_ctor_set(v___x_137_, 12, v_cancelTk_x3f_133_);
lean_ctor_set(v___x_137_, 13, v_inheritedTraceOptions_135_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*14, v_diag_132_);
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*14 + 1, v_suppressElabErrors_134_);
v___x_138_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_116_, v___x_137_, v___y_118_);
lean_dec_ref_known(v___x_137_, 14);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object* v_ref_139_, lean_object* v_msg_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_139_, v_msg_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v_ref_139_);
return v_res_144_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4));
v___x_154_ = l_Lean_stringToMessageData(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object* v_x_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_165_);
v___x_170_ = l_Lean_Syntax_isOfKind(v_x_165_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_172_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_165_, v___x_171_, v_a_166_, v_a_167_);
lean_dec(v_x_165_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = l_Lean_Syntax_getArg(v_x_165_, v___x_173_);
v___x_175_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7));
lean_inc(v___x_174_);
v___x_176_ = l_Lean_Syntax_isOfKind(v___x_174_, v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9));
v___x_178_ = l_Lean_Syntax_isOfKind(v___x_174_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_180_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_165_, v___x_179_, v_a_166_, v_a_167_);
lean_dec(v_x_165_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_x_165_);
v___x_181_ = lean_box(v___x_176_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v___x_174_);
lean_dec(v_x_165_);
v___x_183_ = lean_box(v___x_176_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object* v_x_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_185_, v_a_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object* v_00_u03b1_190_, lean_object* v_ref_191_, lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_191_, v_msg_192_, v___y_193_, v___y_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object* v_00_u03b1_197_, lean_object* v_ref_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(v_00_u03b1_197_, v_ref_198_, v_msg_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v_ref_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object* v_00_u03b1_204_, lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_205_, v___y_206_, v___y_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object* v_00_u03b1_210_, lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(v_00_u03b1_210_, v_msg_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object* v___x_216_, lean_object* v_s_217_, lean_object* v_a_218_, lean_object* v_b_219_){
_start:
{
uint8_t v_decide_220_; 
v_decide_220_ = lean_nat_dec_eq(v_a_218_, v___x_216_);
if (v_decide_220_ == 0)
{
uint32_t v___x_221_; lean_object* v___x_222_; uint32_t v___x_223_; uint8_t v___x_224_; 
v___x_221_ = lean_string_utf8_get_fast(v_s_217_, v_a_218_);
v___x_222_ = lean_string_utf8_next_fast(v_s_217_, v_a_218_);
lean_dec(v_a_218_);
v___x_223_ = 95;
v___x_224_ = lean_uint32_dec_eq(v___x_221_, v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; uint32_t v___x_227_; uint32_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_225_ = lean_unsigned_to_nat(10u);
v___x_226_ = lean_nat_mul(v_b_219_, v___x_225_);
lean_dec(v_b_219_);
v___x_227_ = 48;
v___x_228_ = lean_uint32_sub(v___x_221_, v___x_227_);
v___x_229_ = lean_uint32_to_nat(v___x_228_);
v___x_230_ = lean_nat_add(v___x_226_, v___x_229_);
lean_dec(v___x_229_);
lean_dec(v___x_226_);
v_a_218_ = v___x_222_;
v_b_219_ = v___x_230_;
goto _start;
}
else
{
v_a_218_ = v___x_222_;
goto _start;
}
}
else
{
lean_dec(v_a_218_);
return v_b_219_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object* v___x_233_, lean_object* v_s_234_, lean_object* v_a_235_, lean_object* v_b_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_233_, v_s_234_, v_a_235_, v_b_236_);
lean_dec_ref(v_s_234_);
lean_dec(v___x_233_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object* v_s_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_string_utf8_byte_size(v_s_238_);
lean_inc_ref(v_s_238_);
v___x_241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_241_, 0, v_s_238_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_240_);
v___x_242_ = l_String_Slice_positions(v___x_241_);
lean_dec_ref_known(v___x_241_, 3);
v___x_243_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_240_, v_s_238_, v___x_242_, v___x_239_);
lean_dec_ref(v_s_238_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object* v___x_244_, lean_object* v___x_245_, lean_object* v_s_246_, lean_object* v_inst_247_, lean_object* v_R_248_, lean_object* v_a_249_, lean_object* v_b_250_, lean_object* v_c_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_245_, v_s_246_, v_a_249_, v_b_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object* v___x_253_, lean_object* v___x_254_, lean_object* v_s_255_, lean_object* v_inst_256_, lean_object* v_R_257_, lean_object* v_a_258_, lean_object* v_b_259_, lean_object* v_c_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(v___x_253_, v___x_254_, v_s_255_, v_inst_256_, v_R_257_, v_a_258_, v_b_259_, v_c_260_);
lean_dec_ref(v_s_255_);
lean_dec(v___x_254_);
lean_dec_ref(v___x_253_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object* v_s_262_){
_start:
{
uint32_t v___y_264_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_string_utf8_byte_size(v_s_262_);
lean_inc_ref(v_s_262_);
v___x_289_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_289_, 0, v_s_262_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
lean_ctor_set(v___x_289_, 2, v___x_288_);
v___x_290_ = l_String_Slice_Pos_get_x3f(v___x_289_, v___x_287_);
lean_dec_ref_known(v___x_289_, 3);
if (lean_obj_tag(v___x_290_) == 0)
{
uint32_t v___x_291_; 
v___x_291_ = 65;
v___y_264_ = v___x_291_;
goto v___jp_263_;
}
else
{
lean_object* v_val_292_; uint32_t v___x_293_; 
v_val_292_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_val_292_);
lean_dec_ref_known(v___x_290_, 1);
v___x_293_ = lean_unbox_uint32(v_val_292_);
lean_dec(v_val_292_);
v___y_264_ = v___x_293_;
goto v___jp_263_;
}
v___jp_263_:
{
uint32_t v___x_265_; uint8_t v___x_266_; 
v___x_265_ = 45;
v___x_266_ = lean_uint32_dec_eq(v___y_264_, v___x_265_);
if (v___x_266_ == 0)
{
uint32_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = 43;
v___x_268_ = lean_uint32_dec_eq(v___y_264_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_box(v___x_268_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_s_262_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_string_utf8_byte_size(v_s_262_);
lean_inc_ref(v_s_262_);
v___x_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_274_, 0, v_s_262_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
lean_ctor_set(v___x_274_, 2, v___x_273_);
v___x_275_ = l_String_Slice_Pos_nextn(v___x_274_, v___x_272_, v___x_271_);
lean_dec_ref_known(v___x_274_, 3);
v___x_276_ = lean_string_utf8_extract_fast(v_s_262_, v___x_275_, v___x_273_);
lean_dec(v___x_275_);
lean_dec_ref(v_s_262_);
v___x_277_ = lean_box(v___x_266_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
return v___x_278_;
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_string_utf8_byte_size(v_s_262_);
lean_inc_ref(v_s_262_);
v___x_282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_282_, 0, v_s_262_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
v___x_283_ = l_String_Slice_Pos_nextn(v___x_282_, v___x_280_, v___x_279_);
lean_dec_ref_known(v___x_282_, 3);
v___x_284_ = lean_string_utf8_extract_fast(v_s_262_, v___x_283_, v___x_281_);
lean_dec(v___x_283_);
lean_dec_ref(v_s_262_);
v___x_285_ = lean_box(v___x_266_);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_284_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object* v_s_294_){
_start:
{
lean_object* v_snd_296_; uint32_t v___y_300_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_string_utf8_byte_size(v_s_294_);
lean_inc_ref(v_s_294_);
v___x_321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_321_, 0, v_s_294_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
lean_ctor_set(v___x_321_, 2, v___x_320_);
v___x_322_ = l_String_Slice_Pos_get_x3f(v___x_321_, v___x_319_);
lean_dec_ref_known(v___x_321_, 3);
if (lean_obj_tag(v___x_322_) == 0)
{
uint32_t v___x_323_; 
v___x_323_ = 65;
v___y_300_ = v___x_323_;
goto v___jp_299_;
}
else
{
lean_object* v_val_324_; uint32_t v___x_325_; 
v_val_324_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_val_324_);
lean_dec_ref_known(v___x_322_, 1);
v___x_325_ = lean_unbox_uint32(v_val_324_);
lean_dec(v_val_324_);
v___y_300_ = v___x_325_;
goto v___jp_299_;
}
v___jp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_296_);
v___x_298_ = lean_nat_to_int(v___x_297_);
return v___x_298_;
}
v___jp_299_:
{
uint32_t v___x_301_; uint8_t v___x_302_; 
v___x_301_ = 45;
v___x_302_ = lean_uint32_dec_eq(v___y_300_, v___x_301_);
if (v___x_302_ == 0)
{
uint32_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 43;
v___x_304_ = lean_uint32_dec_eq(v___y_300_, v___x_303_);
if (v___x_304_ == 0)
{
v_snd_296_ = v_s_294_;
goto v___jp_295_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_string_utf8_byte_size(v_s_294_);
lean_inc_ref(v_s_294_);
v___x_308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_308_, 0, v_s_294_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
lean_ctor_set(v___x_308_, 2, v___x_307_);
v___x_309_ = l_String_Slice_Pos_nextn(v___x_308_, v___x_306_, v___x_305_);
lean_dec_ref_known(v___x_308_, 3);
v___x_310_ = lean_string_utf8_extract_fast(v_s_294_, v___x_309_, v___x_307_);
lean_dec(v___x_309_);
lean_dec_ref(v_s_294_);
v_snd_296_ = v___x_310_;
goto v___jp_295_;
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_string_utf8_byte_size(v_s_294_);
lean_inc_ref(v_s_294_);
v___x_314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_314_, 0, v_s_294_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
v___x_315_ = l_String_Slice_Pos_nextn(v___x_314_, v___x_312_, v___x_311_);
lean_dec_ref_known(v___x_314_, 3);
v___x_316_ = lean_string_utf8_extract_fast(v_s_294_, v___x_315_, v___x_313_);
lean_dec(v___x_315_);
lean_dec_ref(v_s_294_);
v___x_317_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v___x_316_);
v___x_318_ = l_Int_negOfNat(v___x_317_);
lean_dec(v___x_317_);
return v___x_318_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3));
v___x_335_ = l_Lean_MessageData_ofFormat(v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object* v_x_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_a_341_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
v___x_345_ = l_Lean_Syntax_isLit_x3f(v___x_344_, v_x_336_);
if (lean_obj_tag(v___x_345_) == 1)
{
lean_object* v_val_346_; 
v_val_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_val_346_);
lean_dec_ref_known(v___x_345_, 1);
v_a_341_ = v_val_346_;
goto v___jp_340_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec(v___x_345_);
v___x_347_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4);
v___x_348_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_336_, v___x_347_, v_a_337_, v_a_338_);
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_a_341_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object* v_x_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_357_, v_a_358_, v_a_359_);
lean_dec(v_a_359_);
lean_dec_ref(v_a_358_);
lean_dec(v_x_357_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object* v___x_362_, lean_object* v_s_363_, lean_object* v_a_364_, lean_object* v_b_365_){
_start:
{
uint8_t v_decide_366_; 
v_decide_366_ = lean_nat_dec_eq(v_a_364_, v___x_362_);
if (v_decide_366_ == 0)
{
lean_object* v_fst_367_; lean_object* v_snd_368_; uint32_t v___x_369_; lean_object* v___x_370_; uint32_t v___x_371_; uint8_t v___x_372_; 
v_fst_367_ = lean_ctor_get(v_b_365_, 0);
v_snd_368_ = lean_ctor_get(v_b_365_, 1);
v___x_369_ = lean_string_utf8_get_fast(v_s_363_, v_a_364_);
v___x_370_ = lean_string_utf8_next_fast(v_s_363_, v_a_364_);
lean_dec(v_a_364_);
v___x_371_ = 95;
v___x_372_ = lean_uint32_dec_eq(v___x_369_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_395_; 
lean_inc(v_snd_368_);
lean_inc(v_fst_367_);
v_isSharedCheck_395_ = !lean_is_exclusive(v_b_365_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; lean_object* v_unused_397_; 
v_unused_396_ = lean_ctor_get(v_b_365_, 1);
lean_dec(v_unused_396_);
v_unused_397_ = lean_ctor_get(v_b_365_, 0);
lean_dec(v_unused_397_);
v___x_374_ = v_b_365_;
v_isShared_375_ = v_isSharedCheck_395_;
goto v_resetjp_373_;
}
else
{
lean_dec(v_b_365_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_395_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
uint32_t v___x_376_; uint8_t v___x_377_; 
v___x_376_ = 46;
v___x_377_ = lean_uint32_dec_eq(v___x_369_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; uint32_t v___x_380_; uint32_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_378_ = lean_unsigned_to_nat(10u);
v___x_379_ = lean_nat_mul(v_fst_367_, v___x_378_);
lean_dec(v_fst_367_);
v___x_380_ = 48;
v___x_381_ = lean_uint32_sub(v___x_369_, v___x_380_);
v___x_382_ = lean_uint32_to_nat(v___x_381_);
v___x_383_ = lean_nat_add(v___x_379_, v___x_382_);
lean_dec(v___x_382_);
lean_dec(v___x_379_);
v___x_384_ = lean_unsigned_to_nat(1u);
v___x_385_ = lean_nat_add(v_snd_368_, v___x_384_);
lean_dec(v_snd_368_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v___x_385_);
lean_ctor_set(v___x_374_, 0, v___x_383_);
v___x_387_ = v___x_374_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_385_);
v___x_387_ = v_reuseFailAlloc_389_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
v_a_364_ = v___x_370_;
v_b_365_ = v___x_387_;
goto _start;
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_392_; 
lean_dec(v_snd_368_);
v___x_390_ = lean_unsigned_to_nat(0u);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v___x_390_);
v___x_392_ = v___x_374_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_fst_367_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___x_390_);
v___x_392_ = v_reuseFailAlloc_394_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
v_a_364_ = v___x_370_;
v_b_365_ = v___x_392_;
goto _start;
}
}
}
}
else
{
v_a_364_ = v___x_370_;
goto _start;
}
}
else
{
lean_dec(v_a_364_);
return v_b_365_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object* v___x_399_, lean_object* v_s_400_, lean_object* v_a_401_, lean_object* v_b_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_399_, v_s_400_, v_a_401_, v_b_402_);
lean_dec_ref(v_s_400_);
lean_dec(v___x_399_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object* v_s_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_string_utf8_byte_size(v_s_404_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_inc_ref(v_s_404_);
v___x_408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_408_, 0, v_s_404_);
lean_ctor_set(v___x_408_, 1, v___x_405_);
lean_ctor_set(v___x_408_, 2, v___x_406_);
v___x_409_ = l_String_Slice_positions(v___x_408_);
lean_dec_ref_known(v___x_408_, 3);
v___x_410_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_406_, v_s_404_, v___x_409_, v___x_407_);
v_fst_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_fst_411_);
v_snd_412_ = lean_ctor_get(v___x_410_, 1);
lean_inc(v_snd_412_);
v___x_413_ = lean_string_length(v_s_404_);
lean_dec_ref(v_s_404_);
v___x_414_ = lean_nat_dec_le(v___x_413_, v_snd_412_);
lean_dec(v_snd_412_);
if (v___x_414_ == 0)
{
lean_dec(v_fst_411_);
return v___x_410_;
}
else
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; lean_object* v_unused_423_; 
v_unused_422_ = lean_ctor_get(v___x_410_, 1);
lean_dec(v_unused_422_);
v_unused_423_ = lean_ctor_get(v___x_410_, 0);
lean_dec(v_unused_423_);
v___x_416_ = v___x_410_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_dec(v___x_410_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_405_);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_fst_411_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v___x_405_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v_s_426_, lean_object* v_inst_427_, lean_object* v_R_428_, lean_object* v_a_429_, lean_object* v_b_430_, lean_object* v_c_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_425_, v_s_426_, v_a_429_, v_b_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v_s_435_, lean_object* v_inst_436_, lean_object* v_R_437_, lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_c_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(v___x_433_, v___x_434_, v_s_435_, v_inst_436_, v_R_437_, v_a_438_, v_b_439_, v_c_440_);
lean_dec_ref(v_s_435_);
lean_dec(v___x_434_);
lean_dec_ref(v___x_433_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object* v_s_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0));
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object* v_s_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v_s_446_);
lean_dec_ref(v_s_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object* v_s_448_, lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v_a_451_, lean_object* v_b_452_){
_start:
{
lean_object* v_it_454_; lean_object* v_startInclusive_455_; lean_object* v_endExclusive_456_; 
if (lean_obj_tag(v_a_451_) == 0)
{
lean_object* v_currPos_461_; lean_object* v_searcher_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_489_; 
v_currPos_461_ = lean_ctor_get(v_a_451_, 0);
v_searcher_462_ = lean_ctor_get(v_a_451_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_489_ == 0)
{
v___x_464_ = v_a_451_;
v_isShared_465_ = v_isSharedCheck_489_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_searcher_462_);
lean_inc(v_currPos_461_);
lean_dec(v_a_451_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_489_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___y_467_; uint8_t v_decide_482_; 
v_decide_482_ = lean_nat_dec_eq(v_searcher_462_, v___x_450_);
if (v_decide_482_ == 0)
{
uint32_t v___x_483_; uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_483_ = lean_string_utf8_get_fast(v_s_448_, v_searcher_462_);
v___x_484_ = 69;
v___x_485_ = lean_uint32_dec_eq(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 101;
v___x_487_ = lean_uint32_dec_eq(v___x_483_, v___x_486_);
v___y_467_ = v___x_487_;
goto v___jp_466_;
}
else
{
v___y_467_ = v___x_485_;
goto v___jp_466_;
}
}
else
{
lean_object* v___x_488_; 
lean_del_object(v___x_464_);
lean_dec(v_searcher_462_);
v___x_488_ = lean_box(1);
lean_inc(v___x_450_);
v_it_454_ = v___x_488_;
v_startInclusive_455_ = v_currPos_461_;
v_endExclusive_456_ = v___x_450_;
goto v___jp_453_;
}
v___jp_466_:
{
if (v___y_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = lean_string_utf8_next_fast(v_s_448_, v_searcher_462_);
lean_dec(v_searcher_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_468_);
v___x_470_ = v___x_464_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_currPos_461_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_472_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
v_a_451_ = v___x_470_;
goto _start;
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_slice_476_; lean_object* v_nextIt_478_; 
v___x_473_ = lean_string_utf8_next_fast(v_s_448_, v_searcher_462_);
v___x_474_ = lean_nat_sub(v___x_473_, v_searcher_462_);
v___x_475_ = lean_nat_add(v_searcher_462_, v___x_474_);
lean_dec(v___x_474_);
v_slice_476_ = l_String_Slice_subslice_x21(v___x_449_, v_currPos_461_, v_searcher_462_);
lean_inc(v___x_475_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_475_);
lean_ctor_set(v___x_464_, 0, v___x_475_);
v_nextIt_478_ = v___x_464_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_475_);
v_nextIt_478_ = v_reuseFailAlloc_481_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v_startInclusive_479_; lean_object* v_endExclusive_480_; 
v_startInclusive_479_ = lean_ctor_get(v_slice_476_, 0);
lean_inc(v_startInclusive_479_);
v_endExclusive_480_ = lean_ctor_get(v_slice_476_, 1);
lean_inc(v_endExclusive_480_);
lean_dec_ref(v_slice_476_);
v_it_454_ = v_nextIt_478_;
v_startInclusive_455_ = v_startInclusive_479_;
v_endExclusive_456_ = v_endExclusive_480_;
goto v___jp_453_;
}
}
}
}
}
else
{
lean_dec(v___x_450_);
lean_dec_ref(v_s_448_);
return v_b_452_;
}
v___jp_453_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_inc_ref(v_s_448_);
v___x_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_457_, 0, v_s_448_);
lean_ctor_set(v___x_457_, 1, v_startInclusive_455_);
lean_ctor_set(v___x_457_, 2, v_endExclusive_456_);
v___x_458_ = l_String_Slice_toString(v___x_457_);
lean_dec_ref_known(v___x_457_, 3);
v___x_459_ = lean_array_push(v_b_452_, v___x_458_);
v_a_451_ = v_it_454_;
v_b_452_ = v___x_459_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object* v_s_490_, lean_object* v___x_491_, lean_object* v___x_492_, lean_object* v_a_493_, lean_object* v_b_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_490_, v___x_491_, v___x_492_, v_a_493_, v_b_494_);
lean_dec_ref(v___x_491_);
return v_res_495_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_nat_to_int(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object* v_s_503_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_string_utf8_byte_size(v_s_503_);
lean_inc_ref(v_s_503_);
v___x_508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_508_, 0, v_s_503_);
lean_ctor_set(v___x_508_, 1, v___x_506_);
lean_ctor_set(v___x_508_, 2, v___x_507_);
v___x_509_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v___x_508_);
v___x_510_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2));
v___x_511_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_503_, v___x_508_, v___x_507_, v___x_509_, v___x_510_);
lean_dec_ref_known(v___x_508_, 3);
v___x_512_ = lean_array_to_list(v___x_511_);
if (lean_obj_tag(v___x_512_) == 1)
{
lean_object* v_tail_513_; 
v_tail_513_ = lean_ctor_get(v___x_512_, 1);
lean_inc(v_tail_513_);
if (lean_obj_tag(v_tail_513_) == 0)
{
lean_object* v_head_514_; lean_object* v___x_515_; lean_object* v_fst_516_; lean_object* v_snd_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_head_514_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_head_514_);
lean_dec_ref_known(v___x_512_, 2);
v___x_515_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_514_);
v_fst_516_ = lean_ctor_get(v___x_515_, 0);
v_snd_517_ = lean_ctor_get(v___x_515_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v___x_515_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_snd_517_);
lean_inc(v_fst_516_);
lean_dec(v___x_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_521_ = l_Int_negOfNat(v_snd_517_);
lean_dec(v_snd_517_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_521_);
v___x_523_ = v___x_519_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_fst_516_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
else
{
lean_object* v_tail_526_; 
v_tail_526_ = lean_ctor_get(v_tail_513_, 1);
if (lean_obj_tag(v_tail_526_) == 0)
{
lean_object* v_head_527_; lean_object* v_head_528_; lean_object* v___x_529_; lean_object* v_fst_530_; lean_object* v_snd_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_541_; 
v_head_527_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_head_527_);
lean_dec_ref_known(v___x_512_, 2);
v_head_528_ = lean_ctor_get(v_tail_513_, 0);
lean_inc(v_head_528_);
lean_dec_ref_known(v_tail_513_, 2);
v___x_529_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_527_);
v_fst_530_ = lean_ctor_get(v___x_529_, 0);
v_snd_531_ = lean_ctor_get(v___x_529_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_541_ == 0)
{
v___x_533_ = v___x_529_;
v_isShared_534_ = v_isSharedCheck_541_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_531_);
lean_inc(v_fst_530_);
lean_dec(v___x_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_541_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_exp_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v_exp_535_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_head_528_);
v___x_536_ = l_Int_negOfNat(v_snd_531_);
lean_dec(v_snd_531_);
v___x_537_ = lean_int_add(v___x_536_, v_exp_535_);
lean_dec(v_exp_535_);
lean_dec(v___x_536_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_537_);
v___x_539_ = v___x_533_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_fst_530_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
else
{
lean_dec_ref_known(v_tail_513_, 2);
lean_dec_ref_known(v___x_512_, 2);
goto v___jp_504_;
}
}
}
else
{
lean_dec(v___x_512_);
goto v___jp_504_;
}
v___jp_504_:
{
lean_object* v___x_505_; 
v___x_505_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object* v_s_542_, lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v_inst_545_, lean_object* v_R_546_, lean_object* v_a_547_, lean_object* v_b_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_542_, v___x_543_, v___x_544_, v_a_547_, v_b_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object* v_s_550_, lean_object* v___x_551_, lean_object* v___x_552_, lean_object* v_inst_553_, lean_object* v_R_554_, lean_object* v_a_555_, lean_object* v_b_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(v_s_550_, v___x_551_, v___x_552_, v_inst_553_, v_R_554_, v_a_555_, v_b_556_);
lean_dec_ref(v___x_551_);
return v_res_557_;
}
}
static double _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2(void){
_start:
{
lean_object* v___x_560_; double v___x_561_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_float_of_nat(v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object* v_s_562_){
_start:
{
lean_object* v___x_563_; lean_object* v_fst_564_; lean_object* v_snd_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_563_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(v_s_562_);
v_fst_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_fst_564_);
v_snd_565_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_snd_565_);
lean_dec_ref(v___x_563_);
v___x_566_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0));
v___x_567_ = lean_string_dec_eq(v_snd_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1));
v___x_569_ = lean_string_dec_eq(v_snd_565_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; lean_object* v___x_573_; uint8_t v___x_574_; lean_object* v___x_575_; double v_flt_576_; uint8_t v___x_577_; 
v___x_570_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(v_snd_565_);
v_fst_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_fst_571_);
v_snd_572_ = lean_ctor_get(v___x_570_, 1);
lean_inc(v_snd_572_);
lean_dec_ref(v___x_570_);
v___x_573_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_574_ = lean_int_dec_lt(v_snd_572_, v___x_573_);
v___x_575_ = lean_nat_abs(v_snd_572_);
lean_dec(v_snd_572_);
v_flt_576_ = l_Float_ofScientific(v_fst_571_, v___x_574_, v___x_575_);
v___x_577_ = lean_unbox(v_fst_564_);
lean_dec(v_fst_564_);
if (v___x_577_ == 0)
{
return v_flt_576_;
}
else
{
double v___x_578_; 
v___x_578_ = lean_float_negate(v_flt_576_);
return v___x_578_;
}
}
else
{
uint8_t v___x_579_; 
lean_dec(v_snd_565_);
v___x_579_ = lean_unbox(v_fst_564_);
lean_dec(v_fst_564_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; double v___x_582_; double v___x_583_; double v___x_584_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = l_Float_ofScientific(v___x_580_, v___x_569_, v___x_581_);
v___x_583_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_584_ = lean_float_div(v___x_582_, v___x_583_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; double v___x_587_; double v___x_588_; double v___x_589_; double v___x_590_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = l_Float_ofScientific(v___x_585_, v___x_569_, v___x_586_);
v___x_588_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_589_ = lean_float_div(v___x_587_, v___x_588_);
v___x_590_ = lean_float_negate(v___x_589_);
return v___x_590_;
}
}
}
else
{
uint8_t v___x_591_; 
lean_dec(v_snd_565_);
v___x_591_ = lean_unbox(v_fst_564_);
lean_dec(v_fst_564_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; double v___x_594_; double v___x_595_; double v___x_596_; 
v___x_592_ = lean_unsigned_to_nat(10u);
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = l_Float_ofScientific(v___x_592_, v___x_567_, v___x_593_);
v___x_595_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_596_ = lean_float_div(v___x_594_, v___x_595_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; double v___x_599_; double v___x_600_; double v___x_601_; double v___x_602_; 
v___x_597_ = lean_unsigned_to_nat(10u);
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = l_Float_ofScientific(v___x_597_, v___x_567_, v___x_598_);
v___x_600_ = lean_float_negate(v___x_599_);
v___x_601_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_602_ = lean_float_div(v___x_600_, v___x_601_);
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object* v_s_603_){
_start:
{
double v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_s_603_);
v_r_605_ = lean_box_float(v_res_604_);
return v_r_605_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3));
v___x_615_ = l_Lean_MessageData_ofFormat(v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object* v_x_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v_a_621_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
v___x_626_ = l_Lean_Syntax_isLit_x3f(v___x_625_, v_x_616_);
if (lean_obj_tag(v___x_626_) == 1)
{
lean_object* v_val_627_; 
v_val_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_val_627_);
lean_dec_ref_known(v___x_626_, 1);
v_a_621_ = v_val_627_;
goto v___jp_620_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v___x_626_);
v___x_628_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4);
v___x_629_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_616_, v___x_628_, v_a_617_, v_a_618_);
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
v___jp_620_:
{
double v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_a_621_);
v___x_623_ = lean_box_float(v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object* v_x_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_x_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object* v___x_643_, lean_object* v___x_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_b_647_){
_start:
{
lean_object* v___x_648_; uint8_t v_decide_649_; 
v___x_648_ = lean_nat_sub(v___x_643_, v___x_644_);
v_decide_649_ = lean_nat_dec_eq(v_a_646_, v___x_648_);
lean_dec(v___x_648_);
if (v_decide_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint32_t v___x_653_; uint32_t v___x_654_; uint8_t v___x_655_; 
v___x_650_ = lean_nat_add(v___x_644_, v_a_646_);
lean_dec(v_a_646_);
v___x_651_ = lean_string_utf8_next_fast(v_a_645_, v___x_650_);
v___x_652_ = lean_nat_sub(v___x_651_, v___x_644_);
v___x_653_ = lean_string_utf8_get_fast(v_a_645_, v___x_650_);
lean_dec(v___x_650_);
v___x_654_ = 95;
v___x_655_ = lean_uint32_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; uint32_t v___x_658_; uint32_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = lean_unsigned_to_nat(2u);
v___x_657_ = lean_nat_mul(v_b_647_, v___x_656_);
lean_dec(v_b_647_);
v___x_658_ = 48;
v___x_659_ = lean_uint32_sub(v___x_653_, v___x_658_);
v___x_660_ = lean_uint32_to_nat(v___x_659_);
v___x_661_ = lean_nat_add(v___x_657_, v___x_660_);
lean_dec(v___x_660_);
lean_dec(v___x_657_);
v_a_646_ = v___x_652_;
v_b_647_ = v___x_661_;
goto _start;
}
else
{
v_a_646_ = v___x_652_;
goto _start;
}
}
else
{
lean_dec(v_a_646_);
return v_b_647_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_b_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_664_, v___x_665_, v_a_666_, v_a_667_, v_b_668_);
lean_dec_ref(v_a_666_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
return v_res_669_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3));
v___x_679_ = l_Lean_MessageData_ofFormat(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object* v_x_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_a_685_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
v___x_696_ = l_Lean_Syntax_isLit_x3f(v___x_695_, v_x_680_);
if (lean_obj_tag(v___x_696_) == 1)
{
lean_object* v_val_697_; 
v_val_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_val_697_);
lean_dec_ref_known(v___x_696_, 1);
v_a_685_ = v_val_697_;
goto v___jp_684_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v___x_696_);
v___x_698_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4);
v___x_699_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_680_, v___x_698_, v_a_681_, v_a_682_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
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
v___jp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_unsigned_to_nat(2u);
v___x_688_ = lean_string_utf8_byte_size(v_a_685_);
lean_inc_ref_n(v_a_685_, 2);
v___x_689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_689_, 0, v_a_685_);
lean_ctor_set(v___x_689_, 1, v___x_686_);
lean_ctor_set(v___x_689_, 2, v___x_688_);
v___x_690_ = l_String_Slice_Pos_nextn(v___x_689_, v___x_686_, v___x_687_);
lean_dec_ref_known(v___x_689_, 3);
lean_inc(v___x_690_);
v___x_691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_691_, 0, v_a_685_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
lean_ctor_set(v___x_691_, 2, v___x_688_);
v___x_692_ = l_String_Slice_positions(v___x_691_);
lean_dec_ref_known(v___x_691_, 3);
v___x_693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_688_, v___x_690_, v_a_685_, v___x_692_, v___x_686_);
lean_dec_ref(v_a_685_);
lean_dec(v___x_690_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object* v_x_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_x_708_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v___x_715_, lean_object* v_a_716_, lean_object* v_inst_717_, lean_object* v_R_718_, lean_object* v_a_719_, lean_object* v_b_720_, lean_object* v_c_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_713_, v___x_714_, v_a_716_, v_a_719_, v_b_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object* v___x_723_, lean_object* v___x_724_, lean_object* v___x_725_, lean_object* v_a_726_, lean_object* v_inst_727_, lean_object* v_R_728_, lean_object* v_a_729_, lean_object* v_b_730_, lean_object* v_c_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(v___x_723_, v___x_724_, v___x_725_, v_a_726_, v_inst_727_, v_R_728_, v_a_729_, v_b_730_, v_c_731_);
lean_dec_ref(v_a_726_);
lean_dec_ref(v___x_725_);
lean_dec(v___x_724_);
lean_dec(v___x_723_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object* v___x_733_, lean_object* v___x_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_b_737_){
_start:
{
lean_object* v___x_738_; uint8_t v_decide_739_; 
v___x_738_ = lean_nat_sub(v___x_733_, v___x_734_);
v_decide_739_ = lean_nat_dec_eq(v_a_736_, v___x_738_);
lean_dec(v___x_738_);
if (v_decide_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint32_t v___x_743_; uint32_t v___x_744_; uint8_t v___x_745_; 
v___x_740_ = lean_nat_add(v___x_734_, v_a_736_);
lean_dec(v_a_736_);
v___x_741_ = lean_string_utf8_next_fast(v_a_735_, v___x_740_);
v___x_742_ = lean_nat_sub(v___x_741_, v___x_734_);
v___x_743_ = lean_string_utf8_get_fast(v_a_735_, v___x_740_);
lean_dec(v___x_740_);
v___x_744_ = 95;
v___x_745_ = lean_uint32_dec_eq(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; uint32_t v___x_748_; uint32_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_746_ = lean_unsigned_to_nat(8u);
v___x_747_ = lean_nat_mul(v_b_737_, v___x_746_);
lean_dec(v_b_737_);
v___x_748_ = 48;
v___x_749_ = lean_uint32_sub(v___x_743_, v___x_748_);
v___x_750_ = lean_uint32_to_nat(v___x_749_);
v___x_751_ = lean_nat_add(v___x_747_, v___x_750_);
lean_dec(v___x_750_);
lean_dec(v___x_747_);
v_a_736_ = v___x_742_;
v_b_737_ = v___x_751_;
goto _start;
}
else
{
v_a_736_ = v___x_742_;
goto _start;
}
}
else
{
lean_dec(v_a_736_);
return v_b_737_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object* v___x_754_, lean_object* v___x_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_b_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_754_, v___x_755_, v_a_756_, v_a_757_, v_b_758_);
lean_dec_ref(v_a_756_);
lean_dec(v___x_755_);
lean_dec(v___x_754_);
return v_res_759_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3));
v___x_769_ = l_Lean_MessageData_ofFormat(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object* v_x_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_a_775_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
v___x_786_ = l_Lean_Syntax_isLit_x3f(v___x_785_, v_x_770_);
if (lean_obj_tag(v___x_786_) == 1)
{
lean_object* v_val_787_; 
v_val_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_val_787_);
lean_dec_ref_known(v___x_786_, 1);
v_a_775_ = v_val_787_;
goto v___jp_774_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec(v___x_786_);
v___x_788_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4);
v___x_789_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_770_, v___x_788_, v_a_771_, v_a_772_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
v___jp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_unsigned_to_nat(2u);
v___x_778_ = lean_string_utf8_byte_size(v_a_775_);
lean_inc_ref_n(v_a_775_, 2);
v___x_779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_779_, 0, v_a_775_);
lean_ctor_set(v___x_779_, 1, v___x_776_);
lean_ctor_set(v___x_779_, 2, v___x_778_);
v___x_780_ = l_String_Slice_Pos_nextn(v___x_779_, v___x_776_, v___x_777_);
lean_dec_ref_known(v___x_779_, 3);
lean_inc(v___x_780_);
v___x_781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_781_, 0, v_a_775_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
lean_ctor_set(v___x_781_, 2, v___x_778_);
v___x_782_ = l_String_Slice_positions(v___x_781_);
lean_dec_ref_known(v___x_781_, 3);
v___x_783_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_778_, v___x_780_, v_a_775_, v___x_782_, v___x_776_);
lean_dec_ref(v_a_775_);
lean_dec(v___x_780_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object* v_x_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_798_, v_a_799_, v_a_800_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_x_798_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object* v___x_803_, lean_object* v___x_804_, lean_object* v___x_805_, lean_object* v_a_806_, lean_object* v_inst_807_, lean_object* v_R_808_, lean_object* v_a_809_, lean_object* v_b_810_, lean_object* v_c_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_803_, v___x_804_, v_a_806_, v_a_809_, v_b_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object* v___x_813_, lean_object* v___x_814_, lean_object* v___x_815_, lean_object* v_a_816_, lean_object* v_inst_817_, lean_object* v_R_818_, lean_object* v_a_819_, lean_object* v_b_820_, lean_object* v_c_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(v___x_813_, v___x_814_, v___x_815_, v_a_816_, v_inst_817_, v_R_818_, v_a_819_, v_b_820_, v_c_821_);
lean_dec_ref(v_a_816_);
lean_dec_ref(v___x_815_);
lean_dec(v___x_814_);
lean_dec(v___x_813_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t v_c_823_){
_start:
{
uint32_t v___x_824_; uint8_t v___x_825_; 
v___x_824_ = 57;
v___x_825_ = lean_uint32_dec_le(v_c_823_, v___x_824_);
if (v___x_825_ == 0)
{
uint32_t v___x_826_; uint8_t v___x_827_; 
v___x_826_ = 70;
v___x_827_ = lean_uint32_dec_le(v_c_823_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; uint32_t v___x_829_; uint32_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_828_ = lean_unsigned_to_nat(10u);
v___x_829_ = 97;
v___x_830_ = lean_uint32_sub(v_c_823_, v___x_829_);
v___x_831_ = lean_uint32_to_nat(v___x_830_);
v___x_832_ = lean_nat_add(v___x_828_, v___x_831_);
lean_dec(v___x_831_);
return v___x_832_;
}
else
{
lean_object* v___x_833_; uint32_t v___x_834_; uint32_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_833_ = lean_unsigned_to_nat(10u);
v___x_834_ = 65;
v___x_835_ = lean_uint32_sub(v_c_823_, v___x_834_);
v___x_836_ = lean_uint32_to_nat(v___x_835_);
v___x_837_ = lean_nat_add(v___x_833_, v___x_836_);
lean_dec(v___x_836_);
return v___x_837_;
}
}
else
{
uint32_t v___x_838_; uint32_t v___x_839_; lean_object* v___x_840_; 
v___x_838_ = 48;
v___x_839_ = lean_uint32_sub(v_c_823_, v___x_838_);
v___x_840_ = lean_uint32_to_nat(v___x_839_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object* v_c_841_){
_start:
{
uint32_t v_c_boxed_842_; lean_object* v_res_843_; 
v_c_boxed_842_ = lean_unbox_uint32(v_c_841_);
lean_dec(v_c_841_);
v_res_843_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v_c_boxed_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object* v___x_844_, lean_object* v___x_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_b_848_){
_start:
{
lean_object* v___x_849_; uint8_t v_decide_850_; 
v___x_849_ = lean_nat_sub(v___x_844_, v___x_845_);
v_decide_850_ = lean_nat_dec_eq(v_a_847_, v___x_849_);
lean_dec(v___x_849_);
if (v_decide_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint32_t v___x_854_; uint32_t v___x_855_; uint8_t v___x_856_; 
v___x_851_ = lean_nat_add(v___x_845_, v_a_847_);
lean_dec(v_a_847_);
v___x_852_ = lean_string_utf8_next_fast(v_a_846_, v___x_851_);
v___x_853_ = lean_nat_sub(v___x_852_, v___x_845_);
v___x_854_ = lean_string_utf8_get_fast(v_a_846_, v___x_851_);
lean_dec(v___x_851_);
v___x_855_ = 95;
v___x_856_ = lean_uint32_dec_eq(v___x_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_857_ = lean_unsigned_to_nat(16u);
v___x_858_ = lean_nat_mul(v_b_848_, v___x_857_);
lean_dec(v_b_848_);
v___x_859_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_854_);
v___x_860_ = lean_nat_add(v___x_858_, v___x_859_);
lean_dec(v___x_859_);
lean_dec(v___x_858_);
v_a_847_ = v___x_853_;
v_b_848_ = v___x_860_;
goto _start;
}
else
{
v_a_847_ = v___x_853_;
goto _start;
}
}
else
{
lean_dec(v_a_847_);
return v_b_848_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object* v___x_863_, lean_object* v___x_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_b_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_863_, v___x_864_, v_a_865_, v_a_866_, v_b_867_);
lean_dec_ref(v_a_865_);
lean_dec(v___x_864_);
lean_dec(v___x_863_);
return v_res_868_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3));
v___x_878_ = l_Lean_MessageData_ofFormat(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object* v_x_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_a_884_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
v___x_895_ = l_Lean_Syntax_isLit_x3f(v___x_894_, v_x_879_);
if (lean_obj_tag(v___x_895_) == 1)
{
lean_object* v_val_896_; 
v_val_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v___x_895_, 1);
v_a_884_ = v_val_896_;
goto v___jp_883_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec(v___x_895_);
v___x_897_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4);
v___x_898_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_879_, v___x_897_, v_a_880_, v_a_881_);
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
v___jp_883_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_unsigned_to_nat(2u);
v___x_887_ = lean_string_utf8_byte_size(v_a_884_);
lean_inc_ref_n(v_a_884_, 2);
v___x_888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_888_, 0, v_a_884_);
lean_ctor_set(v___x_888_, 1, v___x_885_);
lean_ctor_set(v___x_888_, 2, v___x_887_);
v___x_889_ = l_String_Slice_Pos_nextn(v___x_888_, v___x_885_, v___x_886_);
lean_dec_ref_known(v___x_888_, 3);
lean_inc(v___x_889_);
v___x_890_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_890_, 0, v_a_884_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
lean_ctor_set(v___x_890_, 2, v___x_887_);
v___x_891_ = l_String_Slice_positions(v___x_890_);
lean_dec_ref_known(v___x_890_, 3);
v___x_892_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_887_, v___x_889_, v_a_884_, v___x_891_, v___x_885_);
lean_dec_ref(v_a_884_);
lean_dec(v___x_889_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object* v_x_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_x_907_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_a_915_, lean_object* v_inst_916_, lean_object* v_R_917_, lean_object* v_a_918_, lean_object* v_b_919_, lean_object* v_c_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_912_, v___x_913_, v_a_915_, v_a_918_, v_b_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object* v___x_922_, lean_object* v___x_923_, lean_object* v___x_924_, lean_object* v_a_925_, lean_object* v_inst_926_, lean_object* v_R_927_, lean_object* v_a_928_, lean_object* v_b_929_, lean_object* v_c_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(v___x_922_, v___x_923_, v___x_924_, v_a_925_, v_inst_926_, v_R_927_, v_a_928_, v_b_929_, v_c_930_);
lean_dec_ref(v_a_925_);
lean_dec_ref(v___x_924_);
lean_dec(v___x_923_);
lean_dec(v___x_922_);
return v_res_931_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0));
v___x_934_ = l_Lean_stringToMessageData(v___x_933_);
return v___x_934_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5));
v___x_944_ = l_Lean_MessageData_ofFormat(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object* v_x_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_a_950_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
v___x_963_ = l_Lean_Syntax_isLit_x3f(v___x_962_, v_x_945_);
if (lean_obj_tag(v___x_963_) == 1)
{
lean_object* v_val_964_; 
v_val_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_val_964_);
lean_dec_ref_known(v___x_963_, 1);
v_a_950_ = v_val_964_;
goto v___jp_949_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v___x_963_);
v___x_965_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6);
v___x_966_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_945_, v___x_965_, v_a_946_, v_a_947_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
v___jp_949_:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lake_Toml_DateTime_ofString_x3f(v_a_950_);
if (lean_obj_tag(v___x_951_) == 1)
{
lean_object* v_val_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v_val_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_val_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
lean_ctor_set_tag(v___x_954_, 0);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_val_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec(v___x_951_);
v___x_960_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1);
v___x_961_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_945_, v___x_960_, v_a_946_, v_a_947_);
return v___x_961_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object* v_x_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_x_975_);
return v_res_979_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3));
v___x_989_ = l_Lean_MessageData_ofFormat(v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object* v_x_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_a_995_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
v___x_1008_ = l_Lean_Syntax_isLit_x3f(v___x_1007_, v_x_990_);
if (lean_obj_tag(v___x_1008_) == 1)
{
lean_object* v_val_1009_; 
v_val_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v_a_995_ = v_val_1009_;
goto v___jp_994_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec(v___x_1008_);
v___x_1010_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4);
v___x_1011_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_990_, v___x_1010_, v_a_991_, v_a_992_);
return v___x_1011_;
}
v___jp_994_:
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_996_ = lean_unsigned_to_nat(1u);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_string_utf8_byte_size(v_a_995_);
lean_inc_ref_n(v_a_995_, 2);
v___x_999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_999_, 0, v_a_995_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
v___x_1000_ = l_String_Slice_Pos_nextn(v___x_999_, v___x_997_, v___x_996_);
lean_dec_ref_known(v___x_999_, 3);
lean_inc(v___x_1000_);
v___x_1001_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1001_, 0, v_a_995_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
lean_ctor_set(v___x_1001_, 2, v___x_998_);
v___x_1002_ = lean_nat_sub(v___x_998_, v___x_1000_);
v___x_1003_ = l_String_Slice_Pos_prevn(v___x_1001_, v___x_1002_, v___x_996_);
lean_dec_ref_known(v___x_1001_, 3);
v___x_1004_ = lean_nat_add(v___x_1000_, v___x_1003_);
lean_dec(v___x_1003_);
v___x_1005_ = lean_string_utf8_extract_fast(v_a_995_, v___x_1000_, v___x_1004_);
lean_dec(v___x_1004_);
lean_dec(v___x_1000_);
lean_dec_ref(v_a_995_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object* v_x_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_x_1012_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object* v_msg_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = l_String_instInhabitedSlice;
v___x_1019_ = lean_panic_fn_borrowed(v___x_1018_, v_msg_1017_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object* v___y_1020_, lean_object* v_a_1021_, lean_object* v_b_1022_){
_start:
{
lean_object* v_str_1023_; lean_object* v_startInclusive_1024_; lean_object* v_endExclusive_1025_; lean_object* v___x_1026_; uint8_t v_decide_1027_; 
v_str_1023_ = lean_ctor_get(v___y_1020_, 0);
v_startInclusive_1024_ = lean_ctor_get(v___y_1020_, 1);
v_endExclusive_1025_ = lean_ctor_get(v___y_1020_, 2);
v___x_1026_ = lean_nat_sub(v_endExclusive_1025_, v_startInclusive_1024_);
v_decide_1027_ = lean_nat_dec_eq(v_a_1021_, v___x_1026_);
lean_dec(v___x_1026_);
if (v_decide_1027_ == 0)
{
lean_object* v___x_1028_; uint32_t v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1028_ = lean_nat_add(v_startInclusive_1024_, v_a_1021_);
lean_dec(v_a_1021_);
v___x_1029_ = lean_string_utf8_get_fast(v_str_1023_, v___x_1028_);
v___x_1030_ = lean_string_utf8_next_fast(v_str_1023_, v___x_1028_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_nat_sub(v___x_1030_, v_startInclusive_1024_);
v___x_1032_ = lean_unsigned_to_nat(16u);
v___x_1033_ = lean_nat_mul(v_b_1022_, v___x_1032_);
lean_dec(v_b_1022_);
v___x_1034_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_1029_);
v___x_1035_ = lean_nat_add(v___x_1033_, v___x_1034_);
lean_dec(v___x_1034_);
lean_dec(v___x_1033_);
v_a_1021_ = v___x_1031_;
v_b_1022_ = v___x_1035_;
goto _start;
}
else
{
lean_dec(v_a_1021_);
return v_b_1022_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object* v___y_1037_, lean_object* v_a_1038_, lean_object* v_b_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1037_, v_a_1038_, v_b_1039_);
lean_dec_ref(v___y_1037_);
return v_res_1040_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1044_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2));
v___x_1045_ = lean_unsigned_to_nat(14u);
v___x_1046_ = lean_unsigned_to_nat(22u);
v___x_1047_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1));
v___x_1048_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0));
v___x_1049_ = l_mkPanicMessageWithDecl(v___x_1048_, v___x_1047_, v___x_1046_, v___x_1045_, v___x_1044_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object* v_s_1050_){
_start:
{
lean_object* v_str_1051_; lean_object* v_startPos_1052_; lean_object* v_stopPos_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1074_; 
v_str_1051_ = lean_ctor_get(v_s_1050_, 0);
v_startPos_1052_ = lean_ctor_get(v_s_1050_, 1);
v_stopPos_1053_ = lean_ctor_get(v_s_1050_, 2);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_s_1050_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1055_ = v_s_1050_;
v_isShared_1056_ = v_isSharedCheck_1074_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_stopPos_1053_);
lean_inc(v_startPos_1052_);
lean_inc(v_str_1051_);
lean_dec(v_s_1050_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1074_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___y_1059_; uint8_t v___y_1063_; uint8_t v___x_1069_; uint8_t v___y_1071_; uint8_t v___x_1072_; 
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1069_ = lean_string_is_valid_pos(v_str_1051_, v_startPos_1052_);
v___x_1072_ = lean_string_is_valid_pos(v_str_1051_, v_stopPos_1053_);
if (v___x_1072_ == 0)
{
v___y_1071_ = v___x_1072_;
goto v___jp_1070_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_nat_dec_le(v_startPos_1052_, v_stopPos_1053_);
v___y_1071_ = v___x_1073_;
goto v___jp_1070_;
}
v___jp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = l_String_Slice_positions(v___y_1059_);
v___x_1061_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1059_, v___x_1060_, v___x_1057_);
lean_dec_ref(v___y_1059_);
return v___x_1061_;
}
v___jp_1062_:
{
if (v___y_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_del_object(v___x_1055_);
lean_dec(v_stopPos_1053_);
lean_dec(v_startPos_1052_);
lean_dec_ref(v_str_1051_);
v___x_1064_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3);
v___x_1065_ = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(v___x_1064_);
v___y_1059_ = v___x_1065_;
goto v___jp_1058_;
}
else
{
lean_object* v___x_1067_; 
if (v_isShared_1056_ == 0)
{
v___x_1067_ = v___x_1055_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_str_1051_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_startPos_1052_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_stopPos_1053_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
v___y_1059_ = v___x_1067_;
goto v___jp_1058_;
}
}
}
v___jp_1070_:
{
if (v___x_1069_ == 0)
{
v___y_1063_ = v___x_1069_;
goto v___jp_1062_;
}
else
{
v___y_1063_ = v___y_1071_;
goto v___jp_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object* v___y_1075_, lean_object* v_inst_1076_, lean_object* v_R_1077_, lean_object* v_a_1078_, lean_object* v_b_1079_, lean_object* v_c_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1075_, v_a_1078_, v_b_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object* v___y_1082_, lean_object* v_inst_1083_, lean_object* v_R_1084_, lean_object* v_a_1085_, lean_object* v_b_1086_, lean_object* v_c_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(v___y_1082_, v_inst_1083_, v_R_1084_, v_a_1085_, v_b_1086_, v_c_1087_);
lean_dec_ref(v___y_1082_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object* v_s_1089_, lean_object* v_stopPos_1090_, lean_object* v_i_1091_){
_start:
{
uint8_t v___y_1093_; lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = lean_unsigned_to_nat(1u);
v___x_1097_ = lean_nat_add(v_i_1091_, v___x_1096_);
v___x_1098_ = lean_nat_dec_le(v___x_1097_, v_stopPos_1090_);
lean_dec(v___x_1097_);
if (v___x_1098_ == 0)
{
return v_i_1091_;
}
else
{
if (v___x_1098_ == 0)
{
v___y_1093_ = v___x_1098_;
goto v___jp_1092_;
}
else
{
uint32_t v___x_1099_; uint32_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1099_ = lean_string_utf8_get(v_s_1089_, v_i_1091_);
v___x_1100_ = 32;
v___x_1101_ = lean_uint32_dec_eq(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
uint32_t v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = 9;
v___x_1103_ = lean_uint32_dec_eq(v___x_1099_, v___x_1102_);
if (v___x_1103_ == 0)
{
uint32_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = 13;
v___x_1105_ = lean_uint32_dec_eq(v___x_1099_, v___x_1104_);
if (v___x_1105_ == 0)
{
uint32_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = 10;
v___x_1107_ = lean_uint32_dec_eq(v___x_1099_, v___x_1106_);
v___y_1093_ = v___x_1107_;
goto v___jp_1092_;
}
else
{
v___y_1093_ = v___x_1105_;
goto v___jp_1092_;
}
}
else
{
v___y_1093_ = v___x_1103_;
goto v___jp_1092_;
}
}
else
{
v___y_1093_ = v___x_1101_;
goto v___jp_1092_;
}
}
}
v___jp_1092_:
{
if (v___y_1093_ == 0)
{
return v_i_1091_;
}
else
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_string_utf8_next(v_s_1089_, v_i_1091_);
lean_dec(v_i_1091_);
v_i_1091_ = v___x_1094_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object* v_s_1108_, lean_object* v_stopPos_1109_, lean_object* v_i_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_s_1108_, v_stopPos_1109_, v_i_1110_);
lean_dec(v_stopPos_1109_);
lean_dec_ref(v_s_1108_);
return v_res_1111_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0));
v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2));
v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object* v_lit_1118_, lean_object* v_i_1119_, lean_object* v_out_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1134_; uint8_t v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; uint8_t v___y_1139_; lean_object* v_escape_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; uint8_t v___x_1159_; 
v___x_1159_ = lean_string_utf8_at_end(v_lit_1118_, v_i_1119_);
if (v___x_1159_ == 0)
{
uint32_t v_curr_1160_; lean_object* v_i_1161_; uint32_t v___x_1162_; uint8_t v___x_1163_; 
v_curr_1160_ = lean_string_utf8_get_fast(v_lit_1118_, v_i_1119_);
v_i_1161_ = lean_string_utf8_next_fast(v_lit_1118_, v_i_1119_);
lean_dec(v_i_1119_);
v___x_1162_ = 92;
v___x_1163_ = lean_uint32_dec_eq(v_curr_1160_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = lean_string_push(v_out_1120_, v_curr_1160_);
v_i_1119_ = v_i_1161_;
v_out_1120_ = v___x_1164_;
goto _start;
}
else
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_string_utf8_at_end(v_lit_1118_, v_i_1161_);
if (v___x_1166_ == 0)
{
uint32_t v_curr_1167_; lean_object* v_next_1168_; uint32_t v___x_1169_; uint8_t v___x_1170_; 
v_curr_1167_ = lean_string_utf8_get_fast(v_lit_1118_, v_i_1161_);
v_next_1168_ = lean_string_utf8_next_fast(v_lit_1118_, v_i_1161_);
v___x_1169_ = 98;
v___x_1170_ = lean_uint32_dec_eq(v_curr_1167_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 116;
v___x_1172_ = lean_uint32_dec_eq(v_curr_1167_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 110;
v___x_1174_ = lean_uint32_dec_eq(v_curr_1167_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint32_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1175_ = 102;
v___x_1176_ = lean_uint32_dec_eq(v_curr_1167_, v___x_1175_);
if (v___x_1176_ == 0)
{
uint32_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1177_ = 114;
v___x_1178_ = lean_uint32_dec_eq(v_curr_1167_, v___x_1177_);
if (v___x_1178_ == 0)
{
uint32_t v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = 34;
v___x_1180_ = lean_uint32_dec_eq(v_curr_1167_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_uint32_dec_eq(v_curr_1167_, v___x_1162_);
if (v___x_1181_ == 0)
{
uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 117;
v___x_1183_ = lean_uint32_dec_eq(v_curr_1167_, v___x_1182_);
if (v___x_1183_ == 0)
{
uint32_t v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = 85;
v___x_1185_ = lean_uint32_dec_eq(v_curr_1167_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v_b_1187_; 
v___x_1186_ = lean_string_utf8_byte_size(v_lit_1118_);
v_b_1187_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_lit_1118_, v___x_1186_, v_i_1161_);
v_i_1119_ = v_b_1187_;
goto _start;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1189_ = lean_string_utf8_byte_size(v_lit_1118_);
lean_inc_ref_n(v_lit_1118_, 2);
v___x_1190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1190_, 0, v_lit_1118_);
lean_ctor_set(v___x_1190_, 1, v_next_1168_);
lean_ctor_set(v___x_1190_, 2, v___x_1189_);
v___x_1191_ = lean_unsigned_to_nat(8u);
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = l_Substring_Raw_nextn(v___x_1190_, v___x_1191_, v___x_1192_);
lean_dec_ref_known(v___x_1190_, 3);
v___x_1194_ = lean_nat_add(v_next_1168_, v___x_1193_);
lean_dec(v___x_1193_);
v___x_1195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1195_, 0, v_lit_1118_);
lean_ctor_set(v___x_1195_, 1, v_next_1168_);
lean_ctor_set(v___x_1195_, 2, v___x_1194_);
v_escape_1149_ = v___x_1195_;
v___y_1150_ = v_a_1121_;
v___y_1151_ = v_a_1122_;
goto v___jp_1148_;
}
}
else
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1196_ = lean_string_utf8_byte_size(v_lit_1118_);
lean_inc_ref_n(v_lit_1118_, 2);
v___x_1197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1197_, 0, v_lit_1118_);
lean_ctor_set(v___x_1197_, 1, v_next_1168_);
lean_ctor_set(v___x_1197_, 2, v___x_1196_);
v___x_1198_ = lean_unsigned_to_nat(4u);
v___x_1199_ = lean_unsigned_to_nat(0u);
v___x_1200_ = l_Substring_Raw_nextn(v___x_1197_, v___x_1198_, v___x_1199_);
lean_dec_ref_known(v___x_1197_, 3);
v___x_1201_ = lean_nat_add(v_next_1168_, v___x_1200_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1202_, 0, v_lit_1118_);
lean_ctor_set(v___x_1202_, 1, v_next_1168_);
lean_ctor_set(v___x_1202_, 2, v___x_1201_);
v_escape_1149_ = v___x_1202_;
v___y_1150_ = v_a_1121_;
v___y_1151_ = v_a_1122_;
goto v___jp_1148_;
}
}
else
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_string_push(v_out_1120_, v___x_1162_);
v_i_1119_ = v_next_1168_;
v_out_1120_ = v___x_1203_;
goto _start;
}
}
else
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_string_push(v_out_1120_, v___x_1179_);
v_i_1119_ = v_next_1168_;
v_out_1120_ = v___x_1205_;
goto _start;
}
}
else
{
uint32_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = 13;
v___x_1208_ = lean_string_push(v_out_1120_, v___x_1207_);
v_i_1119_ = v_next_1168_;
v_out_1120_ = v___x_1208_;
goto _start;
}
}
else
{
uint32_t v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = 12;
v___x_1211_ = lean_string_push(v_out_1120_, v___x_1210_);
v_i_1119_ = v_next_1168_;
v_out_1120_ = v___x_1211_;
goto _start;
}
}
else
{
uint32_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = 10;
v___x_1214_ = lean_string_push(v_out_1120_, v___x_1213_);
v_i_1119_ = v_next_1168_;
v_out_1120_ = v___x_1214_;
goto _start;
}
}
else
{
uint32_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = 9;
v___x_1217_ = lean_string_push(v_out_1120_, v___x_1216_);
v_i_1119_ = v_next_1168_;
v_out_1120_ = v___x_1217_;
goto _start;
}
}
else
{
uint32_t v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = 8;
v___x_1220_ = lean_string_push(v_out_1120_, v___x_1219_);
v_i_1119_ = v_next_1168_;
v_out_1120_ = v___x_1220_;
goto _start;
}
}
else
{
lean_object* v___x_1222_; 
lean_dec_ref(v_lit_1118_);
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_out_1120_);
return v___x_1222_;
}
}
}
else
{
lean_object* v___x_1223_; 
lean_dec(v_i_1119_);
lean_dec_ref(v_lit_1118_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_out_1120_);
return v___x_1223_;
}
v___jp_1124_:
{
lean_object* v_stopPos_1129_; uint32_t v_ch_1130_; lean_object* v___x_1131_; 
v_stopPos_1129_ = lean_ctor_get(v___y_1128_, 2);
lean_inc(v_stopPos_1129_);
lean_dec_ref(v___y_1128_);
v_ch_1130_ = lean_uint32_of_nat(v___y_1127_);
lean_dec(v___y_1127_);
v___x_1131_ = lean_string_push(v_out_1120_, v_ch_1130_);
v_i_1119_ = v_stopPos_1129_;
v_out_1120_ = v___x_1131_;
v_a_1121_ = v___y_1125_;
v_a_1122_ = v___y_1126_;
goto _start;
}
v___jp_1133_:
{
if (v___y_1135_ == 0)
{
if (v___y_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec(v___y_1137_);
lean_dec_ref(v_out_1120_);
lean_dec_ref(v_lit_1118_);
v___x_1140_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1);
v___x_1141_ = lean_substring_tostring(v___y_1138_);
v___x_1142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
v___x_1143_ = l_Lean_MessageData_ofFormat(v___x_1142_);
v___x_1144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1140_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v___x_1146_, v___y_1134_, v___y_1136_);
return v___x_1147_;
}
else
{
v___y_1125_ = v___y_1134_;
v___y_1126_ = v___y_1136_;
v___y_1127_ = v___y_1137_;
v___y_1128_ = v___y_1138_;
goto v___jp_1124_;
}
}
else
{
v___y_1125_ = v___y_1134_;
v___y_1126_ = v___y_1136_;
v___y_1127_ = v___y_1137_;
v___y_1128_ = v___y_1138_;
goto v___jp_1124_;
}
}
v___jp_1148_:
{
lean_object* v_val_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
lean_inc_ref(v_escape_1149_);
v_val_1152_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(v_escape_1149_);
v___x_1153_ = lean_unsigned_to_nat(55296u);
v___x_1154_ = lean_nat_dec_lt(v_val_1152_, v___x_1153_);
v___x_1155_ = lean_unsigned_to_nat(57343u);
v___x_1156_ = lean_nat_dec_lt(v___x_1155_, v_val_1152_);
if (v___x_1156_ == 0)
{
v___y_1134_ = v___y_1150_;
v___y_1135_ = v___x_1154_;
v___y_1136_ = v___y_1151_;
v___y_1137_ = v_val_1152_;
v___y_1138_ = v_escape_1149_;
v___y_1139_ = v___x_1156_;
goto v___jp_1133_;
}
else
{
lean_object* v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = lean_unsigned_to_nat(1114112u);
v___x_1158_ = lean_nat_dec_lt(v_val_1152_, v___x_1157_);
v___y_1134_ = v___y_1150_;
v___y_1135_ = v___x_1154_;
v___y_1136_ = v___y_1151_;
v___y_1137_ = v_val_1152_;
v___y_1138_ = v_escape_1149_;
v___y_1139_ = v___x_1158_;
goto v___jp_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object* v_lit_1224_, lean_object* v_i_1225_, lean_object* v_out_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v_lit_1224_, v_i_1225_, v_out_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
return v_res_1230_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4));
v___x_1241_ = l_Lean_MessageData_ofFormat(v___x_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object* v_x_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_a_1247_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
v___x_1279_ = l_Lean_Syntax_isLit_x3f(v___x_1278_, v_x_1242_);
if (lean_obj_tag(v___x_1279_) == 1)
{
lean_object* v_val_1280_; 
v_val_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v_a_1247_ = v_val_1280_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec(v___x_1279_);
v___x_1281_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5);
v___x_1282_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1242_, v___x_1281_, v_a_1243_, v_a_1244_);
return v___x_1282_;
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v_fileName_1251_; lean_object* v_fileMap_1252_; lean_object* v_options_1253_; lean_object* v_currRecDepth_1254_; lean_object* v_maxRecDepth_1255_; lean_object* v_ref_1256_; lean_object* v_currNamespace_1257_; lean_object* v_openDecls_1258_; lean_object* v_initHeartbeats_1259_; lean_object* v_maxHeartbeats_1260_; lean_object* v_quotContext_1261_; lean_object* v_currMacroScope_1262_; uint8_t v_diag_1263_; lean_object* v_cancelTk_x3f_1264_; uint8_t v_suppressElabErrors_1265_; lean_object* v_inheritedTraceOptions_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v_ref_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1248_ = lean_unsigned_to_nat(0u);
v___x_1249_ = lean_string_utf8_byte_size(v_a_1247_);
lean_inc_ref_n(v_a_1247_, 2);
v___x_1250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1250_, 0, v_a_1247_);
lean_ctor_set(v___x_1250_, 1, v___x_1248_);
lean_ctor_set(v___x_1250_, 2, v___x_1249_);
v_fileName_1251_ = lean_ctor_get(v_a_1243_, 0);
v_fileMap_1252_ = lean_ctor_get(v_a_1243_, 1);
v_options_1253_ = lean_ctor_get(v_a_1243_, 2);
v_currRecDepth_1254_ = lean_ctor_get(v_a_1243_, 3);
v_maxRecDepth_1255_ = lean_ctor_get(v_a_1243_, 4);
v_ref_1256_ = lean_ctor_get(v_a_1243_, 5);
v_currNamespace_1257_ = lean_ctor_get(v_a_1243_, 6);
v_openDecls_1258_ = lean_ctor_get(v_a_1243_, 7);
v_initHeartbeats_1259_ = lean_ctor_get(v_a_1243_, 8);
v_maxHeartbeats_1260_ = lean_ctor_get(v_a_1243_, 9);
v_quotContext_1261_ = lean_ctor_get(v_a_1243_, 10);
v_currMacroScope_1262_ = lean_ctor_get(v_a_1243_, 11);
v_diag_1263_ = lean_ctor_get_uint8(v_a_1243_, sizeof(void*)*14);
v_cancelTk_x3f_1264_ = lean_ctor_get(v_a_1243_, 12);
v_suppressElabErrors_1265_ = lean_ctor_get_uint8(v_a_1243_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1266_ = lean_ctor_get(v_a_1243_, 13);
v___x_1267_ = lean_unsigned_to_nat(1u);
v___x_1268_ = l_String_Slice_Pos_nextn(v___x_1250_, v___x_1248_, v___x_1267_);
lean_dec_ref_known(v___x_1250_, 3);
lean_inc(v___x_1268_);
v___x_1269_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1269_, 0, v_a_1247_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
lean_ctor_set(v___x_1269_, 2, v___x_1249_);
v___x_1270_ = lean_nat_sub(v___x_1249_, v___x_1268_);
v___x_1271_ = l_String_Slice_Pos_prevn(v___x_1269_, v___x_1270_, v___x_1267_);
lean_dec_ref_known(v___x_1269_, 3);
v___x_1272_ = lean_nat_add(v___x_1268_, v___x_1271_);
lean_dec(v___x_1271_);
v___x_1273_ = lean_string_utf8_extract_fast(v_a_1247_, v___x_1268_, v___x_1272_);
lean_dec(v___x_1272_);
lean_dec(v___x_1268_);
lean_dec_ref(v_a_1247_);
v___x_1274_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1275_ = l_Lean_replaceRef(v_x_1242_, v_ref_1256_);
lean_inc_ref(v_inheritedTraceOptions_1266_);
lean_inc(v_cancelTk_x3f_1264_);
lean_inc(v_currMacroScope_1262_);
lean_inc(v_quotContext_1261_);
lean_inc(v_maxHeartbeats_1260_);
lean_inc(v_initHeartbeats_1259_);
lean_inc(v_openDecls_1258_);
lean_inc(v_currNamespace_1257_);
lean_inc(v_maxRecDepth_1255_);
lean_inc(v_currRecDepth_1254_);
lean_inc_ref(v_options_1253_);
lean_inc_ref(v_fileMap_1252_);
lean_inc_ref(v_fileName_1251_);
v___x_1276_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1276_, 0, v_fileName_1251_);
lean_ctor_set(v___x_1276_, 1, v_fileMap_1252_);
lean_ctor_set(v___x_1276_, 2, v_options_1253_);
lean_ctor_set(v___x_1276_, 3, v_currRecDepth_1254_);
lean_ctor_set(v___x_1276_, 4, v_maxRecDepth_1255_);
lean_ctor_set(v___x_1276_, 5, v_ref_1275_);
lean_ctor_set(v___x_1276_, 6, v_currNamespace_1257_);
lean_ctor_set(v___x_1276_, 7, v_openDecls_1258_);
lean_ctor_set(v___x_1276_, 8, v_initHeartbeats_1259_);
lean_ctor_set(v___x_1276_, 9, v_maxHeartbeats_1260_);
lean_ctor_set(v___x_1276_, 10, v_quotContext_1261_);
lean_ctor_set(v___x_1276_, 11, v_currMacroScope_1262_);
lean_ctor_set(v___x_1276_, 12, v_cancelTk_x3f_1264_);
lean_ctor_set(v___x_1276_, 13, v_inheritedTraceOptions_1266_);
lean_ctor_set_uint8(v___x_1276_, sizeof(void*)*14, v_diag_1263_);
lean_ctor_set_uint8(v___x_1276_, sizeof(void*)*14 + 1, v_suppressElabErrors_1265_);
v___x_1277_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1273_, v___x_1248_, v___x_1274_, v___x_1276_, v_a_1244_);
lean_dec_ref_known(v___x_1276_, 14);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object* v_x_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1283_, v_a_1284_, v_a_1285_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_x_1283_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object* v_s_1288_){
_start:
{
uint32_t v___y_1290_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_string_utf8_byte_size(v_s_1288_);
lean_inc_ref(v_s_1288_);
v___x_1309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1309_, 0, v_s_1288_);
lean_ctor_set(v___x_1309_, 1, v___x_1307_);
lean_ctor_set(v___x_1309_, 2, v___x_1308_);
v___x_1310_ = l_String_Slice_Pos_get_x3f(v___x_1309_, v___x_1307_);
lean_dec_ref_known(v___x_1309_, 3);
if (lean_obj_tag(v___x_1310_) == 0)
{
uint32_t v___x_1311_; 
v___x_1311_ = 65;
v___y_1290_ = v___x_1311_;
goto v___jp_1289_;
}
else
{
lean_object* v_val_1312_; uint32_t v___x_1313_; 
v_val_1312_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_val_1312_);
lean_dec_ref_known(v___x_1310_, 1);
v___x_1313_ = lean_unbox_uint32(v_val_1312_);
lean_dec(v_val_1312_);
v___y_1290_ = v___x_1313_;
goto v___jp_1289_;
}
v___jp_1289_:
{
uint32_t v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = 13;
v___x_1292_ = lean_uint32_dec_eq(v___y_1290_, v___x_1291_);
if (v___x_1292_ == 0)
{
uint32_t v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = 10;
v___x_1294_ = lean_uint32_dec_eq(v___y_1290_, v___x_1293_);
if (v___x_1294_ == 0)
{
return v_s_1288_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = lean_string_utf8_byte_size(v_s_1288_);
lean_inc_ref(v_s_1288_);
v___x_1298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1298_, 0, v_s_1288_);
lean_ctor_set(v___x_1298_, 1, v___x_1296_);
lean_ctor_set(v___x_1298_, 2, v___x_1297_);
v___x_1299_ = l_String_Slice_Pos_nextn(v___x_1298_, v___x_1296_, v___x_1295_);
lean_dec_ref_known(v___x_1298_, 3);
v___x_1300_ = lean_string_utf8_extract_fast(v_s_1288_, v___x_1299_, v___x_1297_);
lean_dec(v___x_1299_);
lean_dec_ref(v_s_1288_);
return v___x_1300_;
}
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1301_ = lean_unsigned_to_nat(2u);
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = lean_string_utf8_byte_size(v_s_1288_);
lean_inc_ref(v_s_1288_);
v___x_1304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1304_, 0, v_s_1288_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
lean_ctor_set(v___x_1304_, 2, v___x_1303_);
v___x_1305_ = l_String_Slice_Pos_nextn(v___x_1304_, v___x_1302_, v___x_1301_);
lean_dec_ref_known(v___x_1304_, 3);
v___x_1306_ = lean_string_utf8_extract_fast(v_s_1288_, v___x_1305_, v___x_1303_);
lean_dec(v___x_1305_);
lean_dec_ref(v_s_1288_);
return v___x_1306_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3));
v___x_1323_ = l_Lean_MessageData_ofFormat(v___x_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object* v_x_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_a_1329_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
v___x_1343_ = l_Lean_Syntax_isLit_x3f(v___x_1342_, v_x_1324_);
if (lean_obj_tag(v___x_1343_) == 1)
{
lean_object* v_val_1344_; 
v_val_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v_a_1329_ = v_val_1344_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v___x_1343_);
v___x_1345_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4);
v___x_1346_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1324_, v___x_1345_, v_a_1325_, v_a_1326_);
return v___x_1346_;
}
v___jp_1328_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1330_ = lean_unsigned_to_nat(3u);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_string_utf8_byte_size(v_a_1329_);
lean_inc_ref_n(v_a_1329_, 2);
v___x_1333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1333_, 0, v_a_1329_);
lean_ctor_set(v___x_1333_, 1, v___x_1331_);
lean_ctor_set(v___x_1333_, 2, v___x_1332_);
v___x_1334_ = l_String_Slice_Pos_nextn(v___x_1333_, v___x_1331_, v___x_1330_);
lean_dec_ref_known(v___x_1333_, 3);
lean_inc(v___x_1334_);
v___x_1335_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1335_, 0, v_a_1329_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
lean_ctor_set(v___x_1335_, 2, v___x_1332_);
v___x_1336_ = lean_nat_sub(v___x_1332_, v___x_1334_);
v___x_1337_ = l_String_Slice_Pos_prevn(v___x_1335_, v___x_1336_, v___x_1330_);
lean_dec_ref_known(v___x_1335_, 3);
v___x_1338_ = lean_nat_add(v___x_1334_, v___x_1337_);
lean_dec(v___x_1337_);
v___x_1339_ = lean_string_utf8_extract_fast(v_a_1329_, v___x_1334_, v___x_1338_);
lean_dec(v___x_1338_);
lean_dec(v___x_1334_);
lean_dec_ref(v_a_1329_);
v___x_1340_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object* v_x_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_x_1347_);
return v_res_1351_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4(void){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3));
v___x_1361_ = l_Lean_MessageData_ofFormat(v___x_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object* v_x_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_a_1367_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
v___x_1400_ = l_Lean_Syntax_isLit_x3f(v___x_1399_, v_x_1362_);
if (lean_obj_tag(v___x_1400_) == 1)
{
lean_object* v_val_1401_; 
v_val_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_val_1401_);
lean_dec_ref_known(v___x_1400_, 1);
v_a_1367_ = v_val_1401_;
goto v___jp_1366_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_dec(v___x_1400_);
v___x_1402_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4);
v___x_1403_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1362_, v___x_1402_, v_a_1363_, v_a_1364_);
return v___x_1403_;
}
v___jp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v_fileName_1371_; lean_object* v_fileMap_1372_; lean_object* v_options_1373_; lean_object* v_currRecDepth_1374_; lean_object* v_maxRecDepth_1375_; lean_object* v_ref_1376_; lean_object* v_currNamespace_1377_; lean_object* v_openDecls_1378_; lean_object* v_initHeartbeats_1379_; lean_object* v_maxHeartbeats_1380_; lean_object* v_quotContext_1381_; lean_object* v_currMacroScope_1382_; uint8_t v_diag_1383_; lean_object* v_cancelTk_x3f_1384_; uint8_t v_suppressElabErrors_1385_; lean_object* v_inheritedTraceOptions_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_ref_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_string_utf8_byte_size(v_a_1367_);
lean_inc_ref_n(v_a_1367_, 2);
v___x_1370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1367_);
lean_ctor_set(v___x_1370_, 1, v___x_1368_);
lean_ctor_set(v___x_1370_, 2, v___x_1369_);
v_fileName_1371_ = lean_ctor_get(v_a_1363_, 0);
v_fileMap_1372_ = lean_ctor_get(v_a_1363_, 1);
v_options_1373_ = lean_ctor_get(v_a_1363_, 2);
v_currRecDepth_1374_ = lean_ctor_get(v_a_1363_, 3);
v_maxRecDepth_1375_ = lean_ctor_get(v_a_1363_, 4);
v_ref_1376_ = lean_ctor_get(v_a_1363_, 5);
v_currNamespace_1377_ = lean_ctor_get(v_a_1363_, 6);
v_openDecls_1378_ = lean_ctor_get(v_a_1363_, 7);
v_initHeartbeats_1379_ = lean_ctor_get(v_a_1363_, 8);
v_maxHeartbeats_1380_ = lean_ctor_get(v_a_1363_, 9);
v_quotContext_1381_ = lean_ctor_get(v_a_1363_, 10);
v_currMacroScope_1382_ = lean_ctor_get(v_a_1363_, 11);
v_diag_1383_ = lean_ctor_get_uint8(v_a_1363_, sizeof(void*)*14);
v_cancelTk_x3f_1384_ = lean_ctor_get(v_a_1363_, 12);
v_suppressElabErrors_1385_ = lean_ctor_get_uint8(v_a_1363_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1386_ = lean_ctor_get(v_a_1363_, 13);
v___x_1387_ = lean_unsigned_to_nat(3u);
v___x_1388_ = l_String_Slice_Pos_nextn(v___x_1370_, v___x_1368_, v___x_1387_);
lean_dec_ref_known(v___x_1370_, 3);
lean_inc(v___x_1388_);
v___x_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1389_, 0, v_a_1367_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
lean_ctor_set(v___x_1389_, 2, v___x_1369_);
v___x_1390_ = lean_nat_sub(v___x_1369_, v___x_1388_);
v___x_1391_ = l_String_Slice_Pos_prevn(v___x_1389_, v___x_1390_, v___x_1387_);
lean_dec_ref_known(v___x_1389_, 3);
v___x_1392_ = lean_nat_add(v___x_1388_, v___x_1391_);
lean_dec(v___x_1391_);
v___x_1393_ = lean_string_utf8_extract_fast(v_a_1367_, v___x_1388_, v___x_1392_);
lean_dec(v___x_1392_);
lean_dec(v___x_1388_);
lean_dec_ref(v_a_1367_);
v___x_1394_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1393_);
v___x_1395_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1396_ = l_Lean_replaceRef(v_x_1362_, v_ref_1376_);
lean_inc_ref(v_inheritedTraceOptions_1386_);
lean_inc(v_cancelTk_x3f_1384_);
lean_inc(v_currMacroScope_1382_);
lean_inc(v_quotContext_1381_);
lean_inc(v_maxHeartbeats_1380_);
lean_inc(v_initHeartbeats_1379_);
lean_inc(v_openDecls_1378_);
lean_inc(v_currNamespace_1377_);
lean_inc(v_maxRecDepth_1375_);
lean_inc(v_currRecDepth_1374_);
lean_inc_ref(v_options_1373_);
lean_inc_ref(v_fileMap_1372_);
lean_inc_ref(v_fileName_1371_);
v___x_1397_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1397_, 0, v_fileName_1371_);
lean_ctor_set(v___x_1397_, 1, v_fileMap_1372_);
lean_ctor_set(v___x_1397_, 2, v_options_1373_);
lean_ctor_set(v___x_1397_, 3, v_currRecDepth_1374_);
lean_ctor_set(v___x_1397_, 4, v_maxRecDepth_1375_);
lean_ctor_set(v___x_1397_, 5, v_ref_1396_);
lean_ctor_set(v___x_1397_, 6, v_currNamespace_1377_);
lean_ctor_set(v___x_1397_, 7, v_openDecls_1378_);
lean_ctor_set(v___x_1397_, 8, v_initHeartbeats_1379_);
lean_ctor_set(v___x_1397_, 9, v_maxHeartbeats_1380_);
lean_ctor_set(v___x_1397_, 10, v_quotContext_1381_);
lean_ctor_set(v___x_1397_, 11, v_currMacroScope_1382_);
lean_ctor_set(v___x_1397_, 12, v_cancelTk_x3f_1384_);
lean_ctor_set(v___x_1397_, 13, v_inheritedTraceOptions_1386_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*14, v_diag_1383_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*14 + 1, v_suppressElabErrors_1385_);
v___x_1398_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1394_, v___x_1368_, v___x_1395_, v___x_1397_, v_a_1364_);
lean_dec_ref_known(v___x_1397_, 14);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object* v_x_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_x_1404_);
return v_res_1408_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2));
v___x_1416_ = l_Lean_stringToMessageData(v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object* v_x_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1421_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_1417_);
v___x_1422_ = l_Lean_Syntax_isOfKind(v_x_1417_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1424_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1417_, v___x_1423_, v_a_1418_, v_a_1419_);
lean_dec(v_x_1417_);
return v___x_1424_;
}
else
{
lean_object* v___x_1425_; lean_object* v_x_1426_; lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1425_ = lean_unsigned_to_nat(0u);
v_x_1426_ = l_Lean_Syntax_getArg(v_x_1417_, v___x_1425_);
v___x_1427_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1426_);
v___x_1428_ = l_Lean_Syntax_isOfKind(v_x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1426_);
v___x_1430_ = l_Lean_Syntax_isOfKind(v_x_1426_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1431_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
lean_inc(v_x_1426_);
v___x_1432_ = l_Lean_Syntax_isOfKind(v_x_1426_, v___x_1431_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1433_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
lean_inc(v_x_1426_);
v___x_1434_ = l_Lean_Syntax_isOfKind(v_x_1426_, v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v_x_1426_);
v___x_1435_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1436_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1417_, v___x_1435_, v_a_1418_, v_a_1419_);
lean_dec(v_x_1417_);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; 
lean_dec(v_x_1417_);
v___x_1437_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1426_, v_a_1418_, v_a_1419_);
lean_dec(v_x_1426_);
return v___x_1437_;
}
}
else
{
lean_object* v___x_1438_; 
lean_dec(v_x_1417_);
v___x_1438_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1426_, v_a_1418_, v_a_1419_);
lean_dec(v_x_1426_);
return v___x_1438_;
}
}
else
{
lean_object* v___x_1439_; 
lean_dec(v_x_1417_);
v___x_1439_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1426_, v_a_1418_, v_a_1419_);
lean_dec(v_x_1426_);
return v___x_1439_;
}
}
else
{
lean_object* v___x_1440_; 
lean_dec(v_x_1417_);
v___x_1440_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1426_, v_a_1418_, v_a_1419_);
lean_dec(v_x_1426_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object* v_x_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_1441_, v_a_1442_, v_a_1443_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
return v_res_1445_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3));
v___x_1455_ = l_Lean_MessageData_ofFormat(v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object* v_x_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1460_; lean_object* v_toApplicative_1461_; lean_object* v_toFunctor_1462_; lean_object* v_toSeq_1463_; lean_object* v_toSeqLeft_1464_; lean_object* v_toSeqRight_1465_; lean_object* v___x_1466_; lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; lean_object* v___f_1472_; lean_object* v___f_1473_; lean_object* v___f_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1460_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_1461_ = lean_ctor_get(v___x_1460_, 0);
v_toFunctor_1462_ = lean_ctor_get(v_toApplicative_1461_, 0);
v_toSeq_1463_ = lean_ctor_get(v_toApplicative_1461_, 2);
v_toSeqLeft_1464_ = lean_ctor_get(v_toApplicative_1461_, 3);
v_toSeqRight_1465_ = lean_ctor_get(v_toApplicative_1461_, 4);
v___x_1466_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
v___f_1467_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_1468_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref_n(v_toFunctor_1462_, 2);
v___f_1469_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1469_, 0, v_toFunctor_1462_);
v___f_1470_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1470_, 0, v_toFunctor_1462_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___f_1469_);
lean_ctor_set(v___x_1471_, 1, v___f_1470_);
lean_inc(v_toSeqRight_1465_);
v___f_1472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1472_, 0, v_toSeqRight_1465_);
lean_inc(v_toSeqLeft_1464_);
v___f_1473_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1473_, 0, v_toSeqLeft_1464_);
lean_inc(v_toSeq_1463_);
v___f_1474_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1474_, 0, v_toSeq_1463_);
v___x_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1471_);
lean_ctor_set(v___x_1475_, 1, v___f_1467_);
lean_ctor_set(v___x_1475_, 2, v___f_1474_);
lean_ctor_set(v___x_1475_, 3, v___f_1473_);
lean_ctor_set(v___x_1475_, 4, v___f_1472_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
lean_ctor_set(v___x_1476_, 1, v___f_1468_);
v___x_1477_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_1478_ = l_Lean_Core_instMonadRefCoreM;
v___x_1479_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_1476_);
v___x_1480_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1479_, v___x_1476_);
v___x_1481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1477_);
lean_ctor_set(v___x_1481_, 1, v___x_1478_);
lean_ctor_set(v___x_1481_, 2, v___x_1480_);
v___x_1482_ = l_Lean_Syntax_isLit_x3f(v___x_1466_, v_x_1456_);
if (lean_obj_tag(v___x_1482_) == 1)
{
lean_object* v_val_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec_ref_known(v___x_1481_, 3);
lean_dec_ref_known(v___x_1476_, 2);
lean_dec(v_x_1456_);
v_val_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_val_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set_tag(v___x_1485_, 0);
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_val_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_object* v___x_1491_; lean_object* v___x_25__overap_1492_; lean_object* v___x_1493_; 
lean_dec(v___x_1482_);
v___x_1491_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_25__overap_1492_ = l_Lean_throwErrorAt___redArg(v___x_1476_, v___x_1481_, v_x_1456_, v___x_1491_);
lean_inc(v_a_1458_);
lean_inc_ref(v_a_1457_);
v___x_1493_ = lean_apply_3(v___x_25__overap_1492_, v_a_1457_, v_a_1458_, lean_box(0));
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object* v_x_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(v_x_1494_, v_a_1495_, v_a_1496_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
return v_res_1498_;
}
}
static lean_object* _init_l_Lake_Toml_elabSimpleKey___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__2));
v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object* v_x_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__1));
lean_inc(v_x_1507_);
v___x_1512_ = l_Lean_Syntax_isOfKind(v_x_1507_, v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1514_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1507_, v___x_1513_, v_a_1508_, v_a_1509_);
lean_dec(v_x_1507_);
return v___x_1514_;
}
else
{
lean_object* v___x_1515_; lean_object* v_x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1515_ = lean_unsigned_to_nat(0u);
v_x_1516_ = l_Lean_Syntax_getArg(v_x_1507_, v___x_1515_);
v___x_1517_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
lean_inc(v_x_1516_);
v___x_1518_ = l_Lean_Syntax_isOfKind(v_x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1519_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1516_);
v___x_1520_ = l_Lean_Syntax_isOfKind(v_x_1516_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1521_; uint8_t v___x_1522_; 
v___x_1521_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1516_);
v___x_1522_ = l_Lean_Syntax_isOfKind(v_x_1516_, v___x_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec(v_x_1516_);
v___x_1523_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1524_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1507_, v___x_1523_, v_a_1508_, v_a_1509_);
lean_dec(v_x_1507_);
return v___x_1524_;
}
else
{
lean_object* v___x_1525_; 
lean_dec(v_x_1507_);
v___x_1525_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1516_, v_a_1508_, v_a_1509_);
lean_dec(v_x_1516_);
return v___x_1525_;
}
}
else
{
lean_object* v___x_1526_; 
lean_dec(v_x_1507_);
v___x_1526_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1516_, v_a_1508_, v_a_1509_);
lean_dec(v_x_1516_);
return v___x_1526_;
}
}
else
{
lean_object* v___x_1527_; 
lean_dec(v_x_1507_);
v___x_1527_ = l_Lean_Syntax_isLit_x3f(v___x_1517_, v_x_1516_);
if (lean_obj_tag(v___x_1527_) == 1)
{
lean_object* v_val_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1535_; 
lean_dec(v_x_1516_);
v_val_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_val_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1535_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1533_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 0);
v___x_1533_ = v___x_1530_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_val_1528_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
lean_dec(v___x_1527_);
v___x_1536_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_1537_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1516_, v___x_1536_, v_a_1508_, v_a_1509_);
lean_dec(v_x_1516_);
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object* v_x_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lake_Toml_elabSimpleKey(v_x_1538_, v_a_1539_, v_a_1540_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object* v_elabVal_1543_, size_t v_sz_1544_, size_t v_i_1545_, lean_object* v_bs_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_usize_dec_lt(v_i_1545_, v_sz_1544_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref(v_elabVal_1543_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_bs_1546_);
return v___x_1551_;
}
else
{
lean_object* v_v_1552_; lean_object* v___x_1553_; 
v_v_1552_ = lean_array_uget_borrowed(v_bs_1546_, v_i_1545_);
lean_inc_ref(v_elabVal_1543_);
lean_inc(v___y_1548_);
lean_inc_ref(v___y_1547_);
lean_inc(v_v_1552_);
v___x_1553_ = lean_apply_4(v_elabVal_1543_, v_v_1552_, v___y_1547_, v___y_1548_, lean_box(0));
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; lean_object* v_bs_x27_1556_; size_t v___x_1557_; size_t v___x_1558_; lean_object* v___x_1559_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = lean_unsigned_to_nat(0u);
v_bs_x27_1556_ = lean_array_uset(v_bs_1546_, v_i_1545_, v___x_1555_);
v___x_1557_ = ((size_t)1ULL);
v___x_1558_ = lean_usize_add(v_i_1545_, v___x_1557_);
v___x_1559_ = lean_array_uset(v_bs_x27_1556_, v_i_1545_, v_a_1554_);
v_i_1545_ = v___x_1558_;
v_bs_1546_ = v___x_1559_;
goto _start;
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec_ref(v_bs_1546_);
lean_dec_ref(v_elabVal_1543_);
v_a_1561_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1553_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1553_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object* v_elabVal_1569_, lean_object* v_sz_1570_, lean_object* v_i_1571_, lean_object* v_bs_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
size_t v_sz_boxed_1576_; size_t v_i_boxed_1577_; lean_object* v_res_1578_; 
v_sz_boxed_1576_ = lean_unbox_usize(v_sz_1570_);
lean_dec(v_sz_1570_);
v_i_boxed_1577_ = lean_unbox_usize(v_i_1571_);
lean_dec(v_i_1571_);
v_res_1578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1569_, v_sz_boxed_1576_, v_i_boxed_1577_, v_bs_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
return v_res_1578_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object* v_x_1587_, lean_object* v_elabVal_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_1587_);
v___x_1593_ = l_Lean_Syntax_isOfKind(v_x_1587_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref(v_elabVal_1588_);
v___x_1594_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3);
v___x_1595_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1587_, v___x_1594_, v_a_1589_, v_a_1590_);
lean_dec(v_x_1587_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_xs_1598_; lean_object* v___x_1599_; size_t v_sz_1600_; size_t v___x_1601_; lean_object* v___x_1602_; 
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = l_Lean_Syntax_getArg(v_x_1587_, v___x_1596_);
lean_dec(v_x_1587_);
v_xs_1598_ = l_Lean_Syntax_getArgs(v___x_1597_);
lean_dec(v___x_1597_);
v___x_1599_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1598_);
lean_dec_ref(v_xs_1598_);
v_sz_1600_ = lean_array_size(v___x_1599_);
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1588_, v_sz_1600_, v___x_1601_, v___x_1599_, v_a_1589_, v_a_1590_);
return v___x_1602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object* v_x_1603_, lean_object* v_elabVal_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1603_, v_elabVal_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object* v_00_u03b1_1609_, lean_object* v_x_1610_, lean_object* v_elabVal_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1610_, v_elabVal_1611_, v_a_1612_, v_a_1613_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object* v_00_u03b1_1616_, lean_object* v_x_1617_, lean_object* v_elabVal_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(v_00_u03b1_1616_, v_x_1617_, v_elabVal_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object* v_00_u03b1_1623_, lean_object* v_elabVal_1624_, size_t v_sz_1625_, size_t v_i_1626_, lean_object* v_bs_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1624_, v_sz_1625_, v_i_1626_, v_bs_1627_, v___y_1628_, v___y_1629_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object* v_00_u03b1_1632_, lean_object* v_elabVal_1633_, lean_object* v_sz_1634_, lean_object* v_i_1635_, lean_object* v_bs_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
size_t v_sz_boxed_1640_; size_t v_i_boxed_1641_; lean_object* v_res_1642_; 
v_sz_boxed_1640_ = lean_unbox_usize(v_sz_1634_);
lean_dec(v_sz_1634_);
v_i_boxed_1641_ = lean_unbox_usize(v_i_1635_);
lean_dec(v_i_1635_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(v_00_u03b1_1632_, v_elabVal_1633_, v_sz_boxed_1640_, v_i_boxed_1641_, v_bs_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(size_t v_sz_1643_, size_t v_i_1644_, lean_object* v_bs_1645_){
_start:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_usize_dec_lt(v_i_1644_, v_sz_1643_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1647_, 0, v_bs_1645_);
return v___x_1647_;
}
else
{
lean_object* v_v_1648_; lean_object* v___x_1649_; lean_object* v_bs_x27_1650_; size_t v___x_1651_; size_t v___x_1652_; lean_object* v___x_1653_; 
v_v_1648_ = lean_array_uget(v_bs_1645_, v_i_1644_);
v___x_1649_ = lean_unsigned_to_nat(0u);
v_bs_x27_1650_ = lean_array_uset(v_bs_1645_, v_i_1644_, v___x_1649_);
v___x_1651_ = ((size_t)1ULL);
v___x_1652_ = lean_usize_add(v_i_1644_, v___x_1651_);
v___x_1653_ = lean_array_uset(v_bs_x27_1650_, v_i_1644_, v_v_1648_);
v_i_1644_ = v___x_1652_;
v_bs_1645_ = v___x_1653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object* v_sz_1655_, lean_object* v_i_1656_, lean_object* v_bs_1657_){
_start:
{
size_t v_sz_boxed_1658_; size_t v_i_boxed_1659_; lean_object* v_res_1660_; 
v_sz_boxed_1658_ = lean_unbox_usize(v_sz_1655_);
lean_dec(v_sz_1655_);
v_i_boxed_1659_ = lean_unbox_usize(v_i_1656_);
lean_dec(v_i_1656_);
v_res_1660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_sz_boxed_1658_, v_i_boxed_1659_, v_bs_1657_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(lean_object* v_msg_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_ref_1665_; lean_object* v___x_1666_; lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1675_; 
v_ref_1665_ = lean_ctor_get(v___y_1662_, 5);
v___x_1666_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_1661_, v___y_1662_, v___y_1663_);
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1675_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1675_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
lean_inc(v_ref_1665_);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v_ref_1665_);
lean_ctor_set(v___x_1671_, 1, v_a_1667_);
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 1);
lean_ctor_set(v___x_1669_, 0, v___x_1671_);
v___x_1673_ = v___x_1669_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(lean_object* v_ref_1681_, lean_object* v_msg_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_fileName_1687_; lean_object* v_fileMap_1688_; lean_object* v_options_1689_; lean_object* v_currRecDepth_1690_; lean_object* v_maxRecDepth_1691_; lean_object* v_ref_1692_; lean_object* v_currNamespace_1693_; lean_object* v_openDecls_1694_; lean_object* v_initHeartbeats_1695_; lean_object* v_maxHeartbeats_1696_; lean_object* v_quotContext_1697_; lean_object* v_currMacroScope_1698_; uint8_t v_diag_1699_; lean_object* v_cancelTk_x3f_1700_; uint8_t v_suppressElabErrors_1701_; lean_object* v_inheritedTraceOptions_1702_; lean_object* v_ref_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_fileName_1687_ = lean_ctor_get(v___y_1684_, 0);
v_fileMap_1688_ = lean_ctor_get(v___y_1684_, 1);
v_options_1689_ = lean_ctor_get(v___y_1684_, 2);
v_currRecDepth_1690_ = lean_ctor_get(v___y_1684_, 3);
v_maxRecDepth_1691_ = lean_ctor_get(v___y_1684_, 4);
v_ref_1692_ = lean_ctor_get(v___y_1684_, 5);
v_currNamespace_1693_ = lean_ctor_get(v___y_1684_, 6);
v_openDecls_1694_ = lean_ctor_get(v___y_1684_, 7);
v_initHeartbeats_1695_ = lean_ctor_get(v___y_1684_, 8);
v_maxHeartbeats_1696_ = lean_ctor_get(v___y_1684_, 9);
v_quotContext_1697_ = lean_ctor_get(v___y_1684_, 10);
v_currMacroScope_1698_ = lean_ctor_get(v___y_1684_, 11);
v_diag_1699_ = lean_ctor_get_uint8(v___y_1684_, sizeof(void*)*14);
v_cancelTk_x3f_1700_ = lean_ctor_get(v___y_1684_, 12);
v_suppressElabErrors_1701_ = lean_ctor_get_uint8(v___y_1684_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1702_ = lean_ctor_get(v___y_1684_, 13);
v_ref_1703_ = l_Lean_replaceRef(v_ref_1681_, v_ref_1692_);
lean_inc_ref(v_inheritedTraceOptions_1702_);
lean_inc(v_cancelTk_x3f_1700_);
lean_inc(v_currMacroScope_1698_);
lean_inc(v_quotContext_1697_);
lean_inc(v_maxHeartbeats_1696_);
lean_inc(v_initHeartbeats_1695_);
lean_inc(v_openDecls_1694_);
lean_inc(v_currNamespace_1693_);
lean_inc(v_maxRecDepth_1691_);
lean_inc(v_currRecDepth_1690_);
lean_inc_ref(v_options_1689_);
lean_inc_ref(v_fileMap_1688_);
lean_inc_ref(v_fileName_1687_);
v___x_1704_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1704_, 0, v_fileName_1687_);
lean_ctor_set(v___x_1704_, 1, v_fileMap_1688_);
lean_ctor_set(v___x_1704_, 2, v_options_1689_);
lean_ctor_set(v___x_1704_, 3, v_currRecDepth_1690_);
lean_ctor_set(v___x_1704_, 4, v_maxRecDepth_1691_);
lean_ctor_set(v___x_1704_, 5, v_ref_1703_);
lean_ctor_set(v___x_1704_, 6, v_currNamespace_1693_);
lean_ctor_set(v___x_1704_, 7, v_openDecls_1694_);
lean_ctor_set(v___x_1704_, 8, v_initHeartbeats_1695_);
lean_ctor_set(v___x_1704_, 9, v_maxHeartbeats_1696_);
lean_ctor_set(v___x_1704_, 10, v_quotContext_1697_);
lean_ctor_set(v___x_1704_, 11, v_currMacroScope_1698_);
lean_ctor_set(v___x_1704_, 12, v_cancelTk_x3f_1700_);
lean_ctor_set(v___x_1704_, 13, v_inheritedTraceOptions_1702_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*14, v_diag_1699_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*14 + 1, v_suppressElabErrors_1701_);
v___x_1705_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_1682_, v___x_1704_, v___y_1685_);
lean_dec_ref_known(v___x_1704_, 14);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg___boxed(lean_object* v_ref_1706_, lean_object* v_msg_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v_ref_1706_, v_msg_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v_ref_1706_);
return v_res_1712_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1));
v___x_1716_ = l_Lean_stringToMessageData(v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object* v_t_1717_, uint8_t v___x_1718_, lean_object* v_as_1719_, size_t v_i_1720_, size_t v_stop_1721_, lean_object* v_b_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_fst_1728_; lean_object* v_snd_1729_; uint8_t v___x_1733_; 
v___x_1733_ = lean_usize_dec_eq(v_i_1720_, v_stop_1721_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_array_uget_borrowed(v_as_1719_, v_i_1720_);
lean_inc(v___x_1734_);
v___x_1735_ = l_Lake_Toml_elabSimpleKey(v___x_1734_, v___y_1724_, v___y_1725_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1756_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1737_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1738_ = l_Lean_Name_str___override(v_b_1722_, v_a_1736_);
lean_inc_ref(v_t_1717_);
lean_inc(v___x_1738_);
v___x_1756_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1737_, v___x_1738_, v_t_1717_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_box(0);
lean_inc(v___x_1738_);
v___x_1758_ = l_Lake_Toml_RBDict_push___redArg(v___x_1737_, v___x_1738_, v___x_1757_, v___y_1723_);
v_fst_1728_ = v___x_1738_;
v_snd_1729_ = v___x_1758_;
goto v___jp_1727_;
}
else
{
lean_object* v_val_1759_; lean_object* v_snd_1760_; 
v_val_1759_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_val_1759_);
lean_dec_ref_known(v___x_1756_, 1);
v_snd_1760_ = lean_ctor_get(v_val_1759_, 1);
lean_inc(v_snd_1760_);
lean_dec(v_val_1759_);
if (lean_obj_tag(v_snd_1760_) == 0)
{
if (v___x_1718_ == 0)
{
goto v___jp_1739_;
}
else
{
v_fst_1728_ = v___x_1738_;
v_snd_1729_ = v___y_1723_;
goto v___jp_1727_;
}
}
else
{
lean_dec_ref_known(v_snd_1760_, 1);
goto v___jp_1739_;
}
}
v___jp_1739_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1740_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
lean_inc(v___x_1738_);
v___x_1741_ = l_Lean_MessageData_ofName(v___x_1738_);
v___x_1742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v___x_1734_, v___x_1744_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec_ref(v___y_1723_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v_snd_1747_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v_snd_1747_ = lean_ctor_get(v_a_1746_, 1);
lean_inc(v_snd_1747_);
lean_dec(v_a_1746_);
v_fst_1728_ = v___x_1738_;
v_snd_1729_ = v_snd_1747_;
goto v___jp_1727_;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v___x_1738_);
lean_dec_ref(v_t_1717_);
v_a_1748_ = lean_ctor_get(v___x_1745_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1745_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1745_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1745_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v___y_1723_);
lean_dec(v_b_1722_);
lean_dec_ref(v_t_1717_);
v_a_1761_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1735_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1735_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec_ref(v_t_1717_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v_b_1722_);
lean_ctor_set(v___x_1769_, 1, v___y_1723_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
return v___x_1770_;
}
v___jp_1727_:
{
size_t v___x_1730_; size_t v___x_1731_; 
v___x_1730_ = ((size_t)1ULL);
v___x_1731_ = lean_usize_add(v_i_1720_, v___x_1730_);
v_i_1720_ = v___x_1731_;
v_b_1722_ = v_fst_1728_;
v___y_1723_ = v_snd_1729_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object* v_t_1771_, lean_object* v___x_1772_, lean_object* v_as_1773_, lean_object* v_i_1774_, lean_object* v_stop_1775_, lean_object* v_b_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
uint8_t v___x_7135__boxed_1781_; size_t v_i_boxed_1782_; size_t v_stop_boxed_1783_; lean_object* v_res_1784_; 
v___x_7135__boxed_1781_ = lean_unbox(v___x_1772_);
v_i_boxed_1782_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_stop_boxed_1783_ = lean_unbox_usize(v_stop_1775_);
lean_dec(v_stop_1775_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_t_1771_, v___x_7135__boxed_1781_, v_as_1773_, v_i_boxed_1782_, v_stop_boxed_1783_, v_b_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec_ref(v_as_1773_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t v___x_1785_, lean_object* v_as_1786_, size_t v_i_1787_, size_t v_stop_1788_, lean_object* v_b_1789_){
_start:
{
lean_object* v___y_1791_; uint8_t v___x_1795_; 
v___x_1795_ = lean_usize_dec_eq(v_i_1787_, v_stop_1788_);
if (v___x_1795_ == 0)
{
lean_object* v_fst_1796_; uint8_t v___x_1797_; 
v_fst_1796_ = lean_ctor_get(v_b_1789_, 0);
v___x_1797_ = lean_unbox(v_fst_1796_);
if (v___x_1797_ == 0)
{
lean_object* v_snd_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1806_; 
v_snd_1798_ = lean_ctor_get(v_b_1789_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_b_1789_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_b_1789_, 0);
lean_dec(v_unused_1807_);
v___x_1800_ = v_b_1789_;
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snd_1798_);
lean_dec(v_b_1789_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1806_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(v___x_1785_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_snd_1798_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
v___y_1791_ = v___x_1804_;
goto v___jp_1790_;
}
}
}
else
{
lean_object* v_snd_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1818_; 
v_snd_1808_ = lean_ctor_get(v_b_1789_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_b_1789_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v_b_1789_, 0);
lean_dec(v_unused_1819_);
v___x_1810_ = v_b_1789_;
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_snd_1808_);
lean_dec(v_b_1789_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1812_ = lean_array_uget_borrowed(v_as_1786_, v_i_1787_);
lean_inc(v___x_1812_);
v___x_1813_ = lean_array_push(v_snd_1808_, v___x_1812_);
v___x_1814_ = lean_box(v___x_1795_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1813_);
lean_ctor_set(v___x_1810_, 0, v___x_1814_);
v___x_1816_ = v___x_1810_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1813_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
v___y_1791_ = v___x_1816_;
goto v___jp_1790_;
}
}
}
}
else
{
return v_b_1789_;
}
v___jp_1790_:
{
size_t v___x_1792_; size_t v___x_1793_; 
v___x_1792_ = ((size_t)1ULL);
v___x_1793_ = lean_usize_add(v_i_1787_, v___x_1792_);
v_i_1787_ = v___x_1793_;
v_b_1789_ = v___y_1791_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object* v___x_1820_, lean_object* v_as_1821_, lean_object* v_i_1822_, lean_object* v_stop_1823_, lean_object* v_b_1824_){
_start:
{
uint8_t v___x_7242__boxed_1825_; size_t v_i_boxed_1826_; size_t v_stop_boxed_1827_; lean_object* v_res_1828_; 
v___x_7242__boxed_1825_ = lean_unbox(v___x_1820_);
v_i_boxed_1826_ = lean_unbox_usize(v_i_1822_);
lean_dec(v_i_1822_);
v_stop_boxed_1827_ = lean_unbox_usize(v_stop_1823_);
lean_dec(v_stop_1823_);
v_res_1828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_7242__boxed_1825_, v_as_1821_, v_i_boxed_1826_, v_stop_boxed_1827_, v_b_1824_);
lean_dec_ref(v_as_1821_);
return v_res_1828_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2));
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object* v_elabVal_1847_, lean_object* v_as_1848_, size_t v_i_1849_, size_t v_stop_1850_, lean_object* v_b_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_a_1856_; lean_object* v___y_1861_; uint8_t v___x_1863_; 
v___x_1863_ = lean_usize_dec_eq(v_i_1849_, v_stop_1850_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1864_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1));
v___x_1865_ = lean_array_uget_borrowed(v_as_1848_, v_i_1849_);
lean_inc(v___x_1865_);
v___x_1866_ = l_Lean_Syntax_isOfKind(v___x_1865_, v___x_1864_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
lean_dec_ref(v_b_1851_);
v___x_1867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3);
v___x_1868_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1865_, v___x_1867_, v___y_1852_, v___y_1853_);
v___y_1861_ = v___x_1868_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = l_Lean_Syntax_getArg(v___x_1865_, v___x_1869_);
v___x_1871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5));
lean_inc(v___x_1870_);
v___x_1872_ = l_Lean_Syntax_isOfKind(v___x_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
lean_dec_ref(v_b_1851_);
v___x_1873_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1874_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1870_, v___x_1873_, v___y_1852_, v___y_1853_);
lean_dec(v___x_1870_);
v___y_1861_ = v___x_1874_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v_v_1877_; lean_object* v___y_1879_; lean_object* v_fst_1880_; lean_object* v_snd_1881_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1927_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1875_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1876_ = lean_unsigned_to_nat(2u);
v_v_1877_ = l_Lean_Syntax_getArg(v___x_1865_, v___x_1876_);
v___x_1948_ = l_Lean_Syntax_getArg(v___x_1870_, v___x_1869_);
v___x_1949_ = l_Lean_Syntax_getArgs(v___x_1948_);
lean_dec(v___x_1948_);
v___x_1950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8));
v___x_1951_ = lean_array_get_size(v___x_1949_);
v___x_1952_ = lean_nat_dec_lt(v___x_1869_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_dec_ref(v___x_1949_);
v___y_1927_ = v___x_1950_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; lean_object* v_snd_1958_; 
v___x_1953_ = lean_box(v___x_1952_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v___x_1950_);
v___x_1955_ = ((size_t)0ULL);
v___x_1956_ = lean_usize_of_nat(v___x_1951_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1872_, v___x_1949_, v___x_1955_, v___x_1956_, v___x_1954_);
lean_dec_ref(v___x_1949_);
v_snd_1958_ = lean_ctor_get(v___x_1957_, 1);
lean_inc(v_snd_1958_);
lean_dec_ref(v___x_1957_);
v___y_1927_ = v_snd_1958_;
goto v___jp_1926_;
}
v___jp_1878_:
{
lean_object* v___x_1882_; 
lean_inc(v___y_1879_);
v___x_1882_ = l_Lake_Toml_elabSimpleKey(v___y_1879_, v___y_1852_, v___y_1853_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1884_ = l_Lean_Name_str___override(v_fst_1880_, v_a_1883_);
lean_inc_ref(v_snd_1881_);
lean_inc(v___x_1884_);
v___x_1885_ = l_Lake_Toml_RBDict_contains___redArg(v___x_1875_, v___x_1884_, v_snd_1881_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; 
lean_dec(v___y_1879_);
lean_inc_ref(v_elabVal_1847_);
lean_inc(v___y_1853_);
lean_inc_ref(v___y_1852_);
v___x_1886_ = lean_apply_4(v_elabVal_1847_, v_v_1877_, v___y_1852_, v___y_1853_, lean_box(0));
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v___x_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1888_, 0, v_a_1887_);
v___x_1889_ = l_Lake_Toml_RBDict_push___redArg(v___x_1875_, v___x_1884_, v___x_1888_, v_snd_1881_);
v_a_1856_ = v___x_1889_;
goto v___jp_1855_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v___x_1884_);
lean_dec_ref(v_snd_1881_);
lean_dec_ref(v_elabVal_1847_);
v_a_1890_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1886_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1886_);
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
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_dec_ref(v_snd_1881_);
lean_dec(v_v_1877_);
v___x_1898_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
v___x_1899_ = l_Lean_MessageData_ofName(v___x_1884_);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___y_1879_, v___x_1902_, v___y_1852_, v___y_1853_);
lean_dec(v___y_1879_);
v___y_1861_ = v___x_1903_;
goto v___jp_1860_;
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec_ref(v_snd_1881_);
lean_dec(v_fst_1880_);
lean_dec(v___y_1879_);
lean_dec(v_v_1877_);
lean_dec_ref(v_elabVal_1847_);
v_a_1904_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1882_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1882_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
v___jp_1912_:
{
if (lean_obj_tag(v___y_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v_fst_1916_; lean_object* v_snd_1917_; 
v_a_1915_ = lean_ctor_get(v___y_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___y_1914_, 1);
v_fst_1916_ = lean_ctor_get(v_a_1915_, 0);
lean_inc(v_fst_1916_);
v_snd_1917_ = lean_ctor_get(v_a_1915_, 1);
lean_inc(v_snd_1917_);
lean_dec(v_a_1915_);
v___y_1879_ = v___y_1913_;
v_fst_1880_ = v_fst_1916_;
v_snd_1881_ = v_snd_1917_;
goto v___jp_1878_;
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v___y_1913_);
lean_dec(v_v_1877_);
lean_dec_ref(v_elabVal_1847_);
v_a_1918_ = lean_ctor_get(v___y_1914_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___y_1914_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___y_1914_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___y_1914_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
v___jp_1926_:
{
size_t v_sz_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v_sz_1928_ = lean_array_size(v___y_1927_);
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_sz_1928_, v___x_1929_, v___y_1927_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_dec(v_v_1877_);
lean_dec_ref(v_b_1851_);
v___x_1931_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1932_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1870_, v___x_1931_, v___y_1852_, v___y_1853_);
lean_dec(v___x_1870_);
v___y_1861_ = v___x_1932_;
goto v___jp_1860_;
}
else
{
lean_object* v_val_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_tailKey_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
lean_dec(v___x_1870_);
v_val_1933_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_val_1933_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1934_ = lean_box(0);
v___x_1935_ = lean_array_get_size(v_val_1933_);
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = lean_nat_sub(v___x_1935_, v___x_1936_);
v_tailKey_1938_ = lean_array_get(v___x_1934_, v_val_1933_, v___x_1937_);
lean_dec(v___x_1937_);
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_array_pop(v_val_1933_);
v___x_1941_ = lean_array_get_size(v___x_1940_);
v___x_1942_ = lean_nat_dec_lt(v___x_1869_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_dec_ref(v___x_1940_);
v___y_1879_ = v_tailKey_1938_;
v_fst_1880_ = v___x_1939_;
v_snd_1881_ = v_b_1851_;
goto v___jp_1878_;
}
else
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_nat_dec_le(v___x_1941_, v___x_1941_);
if (v___x_1943_ == 0)
{
if (v___x_1942_ == 0)
{
lean_dec_ref(v___x_1940_);
v___y_1879_ = v_tailKey_1938_;
v_fst_1880_ = v___x_1939_;
v_snd_1881_ = v_b_1851_;
goto v___jp_1878_;
}
else
{
size_t v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_usize_of_nat(v___x_1941_);
lean_inc_ref(v_b_1851_);
v___x_1945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1851_, v___x_1872_, v___x_1940_, v___x_1929_, v___x_1944_, v___x_1939_, v_b_1851_, v___y_1852_, v___y_1853_);
lean_dec_ref(v___x_1940_);
v___y_1913_ = v_tailKey_1938_;
v___y_1914_ = v___x_1945_;
goto v___jp_1912_;
}
}
else
{
size_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_usize_of_nat(v___x_1941_);
lean_inc_ref(v_b_1851_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1851_, v___x_1872_, v___x_1940_, v___x_1929_, v___x_1946_, v___x_1939_, v_b_1851_, v___y_1852_, v___y_1853_);
lean_dec_ref(v___x_1940_);
v___y_1913_ = v_tailKey_1938_;
v___y_1914_ = v___x_1947_;
goto v___jp_1912_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1959_; 
lean_dec_ref(v_elabVal_1847_);
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_b_1851_);
return v___x_1959_;
}
v___jp_1855_:
{
size_t v___x_1857_; size_t v___x_1858_; 
v___x_1857_ = ((size_t)1ULL);
v___x_1858_ = lean_usize_add(v_i_1849_, v___x_1857_);
v_i_1849_ = v___x_1858_;
v_b_1851_ = v_a_1856_;
goto _start;
}
v___jp_1860_:
{
if (lean_obj_tag(v___y_1861_) == 0)
{
lean_object* v_a_1862_; 
v_a_1862_ = lean_ctor_get(v___y_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___y_1861_, 1);
v_a_1856_ = v_a_1862_;
goto v___jp_1855_;
}
else
{
lean_dec_ref(v_elabVal_1847_);
return v___y_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object* v_elabVal_1960_, lean_object* v_as_1961_, lean_object* v_i_1962_, lean_object* v_stop_1963_, lean_object* v_b_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
size_t v_i_boxed_1968_; size_t v_stop_boxed_1969_; lean_object* v_res_1970_; 
v_i_boxed_1968_ = lean_unbox_usize(v_i_1962_);
lean_dec(v_i_1962_);
v_stop_boxed_1969_ = lean_unbox_usize(v_stop_1963_);
lean_dec(v_stop_1963_);
v_res_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1960_, v_as_1961_, v_i_boxed_1968_, v_stop_boxed_1969_, v_b_1964_, v___y_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v_as_1961_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object* v_as_1971_, size_t v_i_1972_, size_t v_stop_1973_, lean_object* v_b_1974_){
_start:
{
lean_object* v___y_1976_; uint8_t v___x_1980_; 
v___x_1980_ = lean_usize_dec_eq(v_i_1972_, v_stop_1973_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; lean_object* v_snd_1982_; 
v___x_1981_ = lean_array_uget_borrowed(v_as_1971_, v_i_1972_);
v_snd_1982_ = lean_ctor_get(v___x_1981_, 1);
if (lean_obj_tag(v_snd_1982_) == 1)
{
lean_object* v_fst_1983_; lean_object* v_val_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_fst_1983_ = lean_ctor_get(v___x_1981_, 0);
v_val_1984_ = lean_ctor_get(v_snd_1982_, 0);
v___x_1985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
lean_inc(v_val_1984_);
lean_inc(v_fst_1983_);
v___x_1986_ = l_Lake_Toml_RBDict_push___redArg(v___x_1985_, v_fst_1983_, v_val_1984_, v_b_1974_);
v___y_1976_ = v___x_1986_;
goto v___jp_1975_;
}
else
{
v___y_1976_ = v_b_1974_;
goto v___jp_1975_;
}
}
else
{
return v_b_1974_;
}
v___jp_1975_:
{
size_t v___x_1977_; size_t v___x_1978_; 
v___x_1977_ = ((size_t)1ULL);
v___x_1978_ = lean_usize_add(v_i_1972_, v___x_1977_);
v_i_1972_ = v___x_1978_;
v_b_1974_ = v___y_1976_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object* v_as_1987_, lean_object* v_i_1988_, lean_object* v_stop_1989_, lean_object* v_b_1990_){
_start:
{
size_t v_i_boxed_1991_; size_t v_stop_boxed_1992_; lean_object* v_res_1993_; 
v_i_boxed_1991_ = lean_unbox_usize(v_i_1988_);
lean_dec(v_i_1988_);
v_stop_boxed_1992_ = lean_unbox_usize(v_stop_1989_);
lean_dec(v_stop_1989_);
v_res_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_as_1987_, v_i_boxed_1991_, v_stop_boxed_1992_, v_b_1990_);
lean_dec_ref(v_as_1987_);
return v_res_1993_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_2003_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_2002_);
return v___x_2003_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5(void){
_start:
{
lean_object* v___x_2004_; lean_object* v_t_2005_; 
v___x_2004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v_t_2005_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_2004_);
return v_t_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object* v_x_2006_, lean_object* v_elabVal_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2006_);
v___x_2012_ = l_Lean_Syntax_isOfKind(v_x_2006_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec_ref(v_elabVal_2007_);
v___x_2013_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3);
v___x_2014_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2006_, v___x_2013_, v_a_2008_, v_a_2009_);
lean_dec(v_x_2006_);
return v___x_2014_;
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v_kvs_2018_; lean_object* v_a_2020_; lean_object* v___y_2031_; lean_object* v_t_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2015_ = lean_unsigned_to_nat(0u);
v___x_2016_ = lean_unsigned_to_nat(1u);
v___x_2017_ = l_Lean_Syntax_getArg(v_x_2006_, v___x_2016_);
lean_dec(v_x_2006_);
v_kvs_2018_ = l_Lean_Syntax_getArgs(v___x_2017_);
lean_dec(v___x_2017_);
v_t_2041_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5);
v___x_2042_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_kvs_2018_);
lean_dec_ref(v_kvs_2018_);
v___x_2043_ = lean_array_get_size(v___x_2042_);
v___x_2044_ = lean_nat_dec_lt(v___x_2015_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_dec_ref(v___x_2042_);
lean_dec_ref(v_elabVal_2007_);
v_a_2020_ = v_t_2041_;
goto v___jp_2019_;
}
else
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_nat_dec_le(v___x_2043_, v___x_2043_);
if (v___x_2045_ == 0)
{
if (v___x_2044_ == 0)
{
lean_dec_ref(v___x_2042_);
lean_dec_ref(v_elabVal_2007_);
v_a_2020_ = v_t_2041_;
goto v___jp_2019_;
}
else
{
size_t v___x_2046_; size_t v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = ((size_t)0ULL);
v___x_2047_ = lean_usize_of_nat(v___x_2043_);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_2007_, v___x_2042_, v___x_2046_, v___x_2047_, v_t_2041_, v_a_2008_, v_a_2009_);
lean_dec_ref(v___x_2042_);
v___y_2031_ = v___x_2048_;
goto v___jp_2030_;
}
}
else
{
size_t v___x_2049_; size_t v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = ((size_t)0ULL);
v___x_2050_ = lean_usize_of_nat(v___x_2043_);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_2007_, v___x_2042_, v___x_2049_, v___x_2050_, v_t_2041_, v_a_2008_, v_a_2009_);
lean_dec_ref(v___x_2042_);
v___y_2031_ = v___x_2051_;
goto v___jp_2030_;
}
}
v___jp_2019_:
{
lean_object* v_items_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v_items_2021_ = lean_ctor_get(v_a_2020_, 0);
lean_inc_ref(v_items_2021_);
lean_dec_ref(v_a_2020_);
v___x_2022_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
v___x_2023_ = lean_array_get_size(v_items_2021_);
v___x_2024_ = lean_nat_dec_lt(v___x_2015_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
lean_dec_ref(v_items_2021_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2022_);
return v___x_2025_;
}
else
{
size_t v___x_2026_; size_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2026_ = ((size_t)0ULL);
v___x_2027_ = lean_usize_of_nat(v___x_2023_);
v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_2021_, v___x_2026_, v___x_2027_, v___x_2022_);
lean_dec_ref(v_items_2021_);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
return v___x_2029_;
}
}
v___jp_2030_:
{
if (lean_obj_tag(v___y_2031_) == 0)
{
lean_object* v_a_2032_; 
v_a_2032_ = lean_ctor_get(v___y_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___y_2031_, 1);
v_a_2020_ = v_a_2032_;
goto v___jp_2019_;
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_a_2033_ = lean_ctor_get(v___y_2031_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___y_2031_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___y_2031_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___y_2031_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object* v_x_2052_, lean_object* v_elabVal_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2052_, v_elabVal_2053_, v_a_2054_, v_a_2055_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(lean_object* v_00_u03b1_2058_, lean_object* v_ref_2059_, lean_object* v_msg_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v_ref_2059_, v_msg_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object* v_00_u03b1_2066_, lean_object* v_ref_2067_, lean_object* v_msg_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_00_u03b1_2066_, v_ref_2067_, v_msg_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v_ref_2067_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(lean_object* v_00_u03b1_2074_, lean_object* v_msg_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_2075_, v___y_2077_, v___y_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2081_, lean_object* v_msg_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(v_00_u03b1_2081_, v_msg_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2087_;
}
}
static lean_object* _init_l_Lake_Toml_elabVal___closed__1(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = ((lean_object*)(l_Lake_Toml_elabVal___closed__0));
v___x_2090_ = l_Lean_stringToMessageData(v___x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object* v_x_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lake_Toml_elabVal(v_x_2091_, v_a_2092_, v_a_2093_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object* v_x_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_){
_start:
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
lean_inc(v_x_2096_);
v___x_2101_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
lean_inc(v_x_2096_);
v___x_2103_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2102_);
if (v___x_2103_ == 0)
{
lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
lean_inc(v_x_2096_);
v___x_2105_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2104_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2106_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
lean_inc(v_x_2096_);
v___x_2107_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
lean_inc(v_x_2096_);
v___x_2109_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
lean_inc(v_x_2096_);
v___x_2111_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_2096_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_2096_);
v___x_2115_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_2096_);
v___x_2117_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2096_);
v___x_2119_ = l_Lean_Syntax_isOfKind(v_x_2096_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_obj_once(&l_Lake_Toml_elabVal___closed__1, &l_Lake_Toml_elabVal___closed__1_once, _init_l_Lake_Toml_elabVal___closed__1);
v___x_2121_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2096_, v___x_2120_, v_a_2097_, v_a_2098_);
lean_dec(v_x_2096_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2096_);
v___x_2123_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2096_, v___x_2122_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2132_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2132_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2132_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2128_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2128_, 0, v_x_2096_);
lean_ctor_set(v___x_2128_, 1, v_a_2124_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2128_);
v___x_2130_ = v___x_2126_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_x_2096_);
v_a_2133_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2123_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2123_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2096_);
v___x_2142_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_2096_, v___x_2141_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2151_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2147_, 0, v_x_2096_);
lean_ctor_set(v___x_2147_, 1, v_a_2143_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2147_);
v___x_2149_ = v___x_2145_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v_x_2096_);
v_a_2152_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2142_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2142_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
else
{
lean_object* v___x_2160_; 
lean_inc(v_x_2096_);
v___x_2160_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2170_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2170_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_2165_, 0, v_x_2096_);
v___x_2166_ = lean_unbox(v_a_2161_);
lean_dec(v_a_2161_);
lean_ctor_set_uint8(v___x_2165_, sizeof(void*)*1, v___x_2166_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2165_);
v___x_2168_ = v___x_2163_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2165_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_x_2096_);
v_a_2171_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2160_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2160_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
else
{
lean_object* v___x_2179_; 
lean_inc(v_x_2096_);
v___x_2179_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2188_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2184_, 0, v_x_2096_);
lean_ctor_set(v___x_2184_, 1, v_a_2180_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2184_);
v___x_2186_ = v___x_2182_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_x_2096_);
v_a_2189_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2179_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2179_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
else
{
lean_object* v___x_2197_; 
v___x_2197_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2206_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2200_ = v___x_2197_;
v_isShared_2201_ = v_isSharedCheck_2206_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2197_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2206_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2202_, 0, v_x_2096_);
lean_ctor_set(v___x_2202_, 1, v_a_2198_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2202_);
v___x_2204_ = v___x_2200_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_x_2096_);
v_a_2207_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2197_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2197_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
else
{
lean_object* v___x_2215_; 
v___x_2215_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2225_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2225_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2225_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2220_ = lean_nat_to_int(v_a_2216_);
v___x_2221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2221_, 0, v_x_2096_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2221_);
v___x_2223_ = v___x_2218_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec(v_x_2096_);
v_a_2226_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2215_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2215_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
else
{
lean_object* v___x_2234_; 
v___x_2234_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2244_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2237_ = v___x_2234_;
v_isShared_2238_ = v_isSharedCheck_2244_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2234_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2244_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2239_ = lean_nat_to_int(v_a_2235_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v_x_2096_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2240_);
v___x_2242_ = v___x_2237_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_x_2096_);
v_a_2245_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2234_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2234_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
else
{
lean_object* v___x_2253_; 
v___x_2253_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2263_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2263_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2263_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2258_ = lean_nat_to_int(v_a_2254_);
v___x_2259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_x_2096_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2259_);
v___x_2261_ = v___x_2256_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_x_2096_);
v_a_2264_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2253_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2253_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
else
{
lean_object* v___x_2272_; 
v___x_2272_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2281_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2277_, 0, v_x_2096_);
lean_ctor_set(v___x_2277_, 1, v_a_2273_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2277_);
v___x_2279_ = v___x_2275_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v_x_2096_);
v_a_2282_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2272_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2272_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
else
{
lean_object* v___x_2290_; 
v___x_2290_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_2096_, v_a_2097_, v_a_2098_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2300_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2293_ = v___x_2290_;
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2300_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; double v___x_2296_; lean_object* v___x_2298_; 
v___x_2295_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_2295_, 0, v_x_2096_);
v___x_2296_ = lean_unbox_float(v_a_2291_);
lean_dec(v_a_2291_);
lean_ctor_set_float(v___x_2295_, sizeof(void*)*1, v___x_2296_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2295_);
v___x_2298_ = v___x_2293_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2295_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec(v_x_2096_);
v_a_2301_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2290_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2290_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
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
}
}
lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
