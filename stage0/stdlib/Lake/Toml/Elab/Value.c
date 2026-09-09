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
lean_object* v___x_82_; lean_object* v_toCold_83_; lean_object* v_env_84_; lean_object* v_options_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_toCold_83_ = lean_ctor_get(v___y_79_, 0);
v_env_84_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_82_);
v_options_85_ = lean_ctor_get(v_toCold_83_, 2);
v___x_86_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2);
v___x_87_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_85_);
v___x_88_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_88_, 0, v_env_84_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
lean_ctor_set(v___x_88_, 3, v_options_85_);
v___x_89_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_msgData_78_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msgData_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object* v_msg_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_ref_100_; lean_object* v___x_101_; lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_110_; 
v_ref_100_ = lean_ctor_get(v___y_97_, 2);
v___x_101_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_96_, v___y_97_, v___y_98_);
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_110_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_110_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
lean_inc(v_ref_100_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_ref_100_);
lean_ctor_set(v___x_106_, 1, v_a_102_);
if (v_isShared_105_ == 0)
{
lean_ctor_set_tag(v___x_104_, 1);
lean_ctor_set(v___x_104_, 0, v___x_106_);
v___x_108_ = v___x_104_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_111_, v___y_112_, v___y_113_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object* v_ref_116_, lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_toCold_121_; lean_object* v_currRecDepth_122_; lean_object* v_ref_123_; uint8_t v_diag_124_; uint8_t v_suppressElabErrors_125_; lean_object* v_ref_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_toCold_121_ = lean_ctor_get(v___y_118_, 0);
v_currRecDepth_122_ = lean_ctor_get(v___y_118_, 1);
v_ref_123_ = lean_ctor_get(v___y_118_, 2);
v_diag_124_ = lean_ctor_get_uint8(v___y_118_, sizeof(void*)*3);
v_suppressElabErrors_125_ = lean_ctor_get_uint8(v___y_118_, sizeof(void*)*3 + 1);
v_ref_126_ = l_Lean_replaceRef(v_ref_116_, v_ref_123_);
lean_inc(v_currRecDepth_122_);
lean_inc_ref(v_toCold_121_);
v___x_127_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_127_, 0, v_toCold_121_);
lean_ctor_set(v___x_127_, 1, v_currRecDepth_122_);
lean_ctor_set(v___x_127_, 2, v_ref_126_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*3, v_diag_124_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*3 + 1, v_suppressElabErrors_125_);
v___x_128_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_117_, v___x_127_, v___y_119_);
lean_dec_ref_known(v___x_127_, 3);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object* v_ref_129_, lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_129_, v_msg_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v_ref_129_);
return v_res_134_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4));
v___x_144_ = l_Lean_stringToMessageData(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object* v_x_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_155_);
v___x_160_ = l_Lean_Syntax_isOfKind(v_x_155_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_162_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_155_, v___x_161_, v_a_156_, v_a_157_);
lean_dec(v_x_155_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = l_Lean_Syntax_getArg(v_x_155_, v___x_163_);
v___x_165_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7));
lean_inc(v___x_164_);
v___x_166_ = l_Lean_Syntax_isOfKind(v___x_164_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9));
v___x_168_ = l_Lean_Syntax_isOfKind(v___x_164_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_170_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_155_, v___x_169_, v_a_156_, v_a_157_);
lean_dec(v_x_155_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec(v_x_155_);
v___x_171_ = lean_box(v___x_166_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v___x_164_);
lean_dec(v_x_155_);
v___x_173_ = lean_box(v___x_166_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_175_, v_a_176_, v_a_177_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object* v_00_u03b1_180_, lean_object* v_ref_181_, lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_181_, v_msg_182_, v___y_183_, v___y_184_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object* v_00_u03b1_187_, lean_object* v_ref_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(v_00_u03b1_187_, v_ref_188_, v_msg_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v_ref_188_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object* v_00_u03b1_194_, lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_195_, v___y_196_, v___y_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object* v_00_u03b1_200_, lean_object* v_msg_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(v_00_u03b1_200_, v_msg_201_, v___y_202_, v___y_203_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object* v___x_206_, lean_object* v_s_207_, lean_object* v_a_208_, lean_object* v_b_209_){
_start:
{
uint8_t v_decide_210_; 
v_decide_210_ = lean_nat_dec_eq(v_a_208_, v___x_206_);
if (v_decide_210_ == 0)
{
uint32_t v___x_211_; lean_object* v___x_212_; uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_211_ = lean_string_utf8_get_fast(v_s_207_, v_a_208_);
v___x_212_ = lean_string_utf8_next_fast(v_s_207_, v_a_208_);
lean_dec(v_a_208_);
v___x_213_ = 95;
v___x_214_ = lean_uint32_dec_eq(v___x_211_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; uint32_t v___x_217_; uint32_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_215_ = lean_unsigned_to_nat(10u);
v___x_216_ = lean_nat_mul(v_b_209_, v___x_215_);
lean_dec(v_b_209_);
v___x_217_ = 48;
v___x_218_ = lean_uint32_sub(v___x_211_, v___x_217_);
v___x_219_ = lean_uint32_to_nat(v___x_218_);
v___x_220_ = lean_nat_add(v___x_216_, v___x_219_);
lean_dec(v___x_219_);
lean_dec(v___x_216_);
v_a_208_ = v___x_212_;
v_b_209_ = v___x_220_;
goto _start;
}
else
{
v_a_208_ = v___x_212_;
goto _start;
}
}
else
{
lean_dec(v_a_208_);
return v_b_209_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object* v___x_223_, lean_object* v_s_224_, lean_object* v_a_225_, lean_object* v_b_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_223_, v_s_224_, v_a_225_, v_b_226_);
lean_dec_ref(v_s_224_);
lean_dec(v___x_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object* v_s_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_string_utf8_byte_size(v_s_228_);
lean_inc_ref(v_s_228_);
v___x_231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_231_, 0, v_s_228_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
lean_ctor_set(v___x_231_, 2, v___x_230_);
v___x_232_ = l_String_Slice_positions(v___x_231_);
lean_dec_ref_known(v___x_231_, 3);
v___x_233_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_230_, v_s_228_, v___x_232_, v___x_229_);
lean_dec_ref(v_s_228_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object* v___x_234_, lean_object* v___x_235_, lean_object* v_s_236_, lean_object* v_inst_237_, lean_object* v_R_238_, lean_object* v_a_239_, lean_object* v_b_240_, lean_object* v_c_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_235_, v_s_236_, v_a_239_, v_b_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object* v___x_243_, lean_object* v___x_244_, lean_object* v_s_245_, lean_object* v_inst_246_, lean_object* v_R_247_, lean_object* v_a_248_, lean_object* v_b_249_, lean_object* v_c_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(v___x_243_, v___x_244_, v_s_245_, v_inst_246_, v_R_247_, v_a_248_, v_b_249_, v_c_250_);
lean_dec_ref(v_s_245_);
lean_dec(v___x_244_);
lean_dec_ref(v___x_243_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object* v_s_252_){
_start:
{
uint32_t v___y_254_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_string_utf8_byte_size(v_s_252_);
lean_inc_ref(v_s_252_);
v___x_279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_279_, 0, v_s_252_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
lean_ctor_set(v___x_279_, 2, v___x_278_);
v___x_280_ = l_String_Slice_Pos_get_x3f(v___x_279_, v___x_277_);
lean_dec_ref_known(v___x_279_, 3);
if (lean_obj_tag(v___x_280_) == 0)
{
uint32_t v___x_281_; 
v___x_281_ = 65;
v___y_254_ = v___x_281_;
goto v___jp_253_;
}
else
{
lean_object* v_val_282_; uint32_t v___x_283_; 
v_val_282_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v___x_280_, 1);
v___x_283_ = lean_unbox_uint32(v_val_282_);
lean_dec(v_val_282_);
v___y_254_ = v___x_283_;
goto v___jp_253_;
}
v___jp_253_:
{
uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = 45;
v___x_256_ = lean_uint32_dec_eq(v___y_254_, v___x_255_);
if (v___x_256_ == 0)
{
uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = 43;
v___x_258_ = lean_uint32_dec_eq(v___y_254_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(v___x_258_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_s_252_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_string_utf8_byte_size(v_s_252_);
lean_inc_ref(v_s_252_);
v___x_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_264_, 0, v_s_252_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_263_);
v___x_265_ = l_String_Slice_Pos_nextn(v___x_264_, v___x_262_, v___x_261_);
lean_dec_ref_known(v___x_264_, 3);
v___x_266_ = lean_string_utf8_extract_fast(v_s_252_, v___x_265_, v___x_263_);
lean_dec(v___x_265_);
lean_dec_ref(v_s_252_);
v___x_267_ = lean_box(v___x_256_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
return v___x_268_;
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_string_utf8_byte_size(v_s_252_);
lean_inc_ref(v_s_252_);
v___x_272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_272_, 0, v_s_252_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
lean_ctor_set(v___x_272_, 2, v___x_271_);
v___x_273_ = l_String_Slice_Pos_nextn(v___x_272_, v___x_270_, v___x_269_);
lean_dec_ref_known(v___x_272_, 3);
v___x_274_ = lean_string_utf8_extract_fast(v_s_252_, v___x_273_, v___x_271_);
lean_dec(v___x_273_);
lean_dec_ref(v_s_252_);
v___x_275_ = lean_box(v___x_256_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object* v_s_284_){
_start:
{
lean_object* v_snd_286_; uint32_t v___y_290_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_string_utf8_byte_size(v_s_284_);
lean_inc_ref(v_s_284_);
v___x_311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_311_, 0, v_s_284_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
lean_ctor_set(v___x_311_, 2, v___x_310_);
v___x_312_ = l_String_Slice_Pos_get_x3f(v___x_311_, v___x_309_);
lean_dec_ref_known(v___x_311_, 3);
if (lean_obj_tag(v___x_312_) == 0)
{
uint32_t v___x_313_; 
v___x_313_ = 65;
v___y_290_ = v___x_313_;
goto v___jp_289_;
}
else
{
lean_object* v_val_314_; uint32_t v___x_315_; 
v_val_314_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_val_314_);
lean_dec_ref_known(v___x_312_, 1);
v___x_315_ = lean_unbox_uint32(v_val_314_);
lean_dec(v_val_314_);
v___y_290_ = v___x_315_;
goto v___jp_289_;
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_286_);
v___x_288_ = lean_nat_to_int(v___x_287_);
return v___x_288_;
}
v___jp_289_:
{
uint32_t v___x_291_; uint8_t v___x_292_; 
v___x_291_ = 45;
v___x_292_ = lean_uint32_dec_eq(v___y_290_, v___x_291_);
if (v___x_292_ == 0)
{
uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = 43;
v___x_294_ = lean_uint32_dec_eq(v___y_290_, v___x_293_);
if (v___x_294_ == 0)
{
v_snd_286_ = v_s_284_;
goto v___jp_285_;
}
else
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_string_utf8_byte_size(v_s_284_);
lean_inc_ref(v_s_284_);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v_s_284_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
lean_ctor_set(v___x_298_, 2, v___x_297_);
v___x_299_ = l_String_Slice_Pos_nextn(v___x_298_, v___x_296_, v___x_295_);
lean_dec_ref_known(v___x_298_, 3);
v___x_300_ = lean_string_utf8_extract_fast(v_s_284_, v___x_299_, v___x_297_);
lean_dec(v___x_299_);
lean_dec_ref(v_s_284_);
v_snd_286_ = v___x_300_;
goto v___jp_285_;
}
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_string_utf8_byte_size(v_s_284_);
lean_inc_ref(v_s_284_);
v___x_304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_304_, 0, v_s_284_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_303_);
v___x_305_ = l_String_Slice_Pos_nextn(v___x_304_, v___x_302_, v___x_301_);
lean_dec_ref_known(v___x_304_, 3);
v___x_306_ = lean_string_utf8_extract_fast(v_s_284_, v___x_305_, v___x_303_);
lean_dec(v___x_305_);
lean_dec_ref(v_s_284_);
v___x_307_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v___x_306_);
v___x_308_ = l_Int_negOfNat(v___x_307_);
lean_dec(v___x_307_);
return v___x_308_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3));
v___x_325_ = l_Lean_MessageData_ofFormat(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_a_331_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
v___x_335_ = l_Lean_Syntax_isLit_x3f(v___x_334_, v_x_326_);
if (lean_obj_tag(v___x_335_) == 1)
{
lean_object* v_val_336_; 
v_val_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_val_336_);
lean_dec_ref_known(v___x_335_, 1);
v_a_331_ = v_val_336_;
goto v___jp_330_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v___x_335_);
v___x_337_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4);
v___x_338_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_326_, v___x_337_, v_a_327_, v_a_328_);
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
v___jp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_a_331_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object* v_x_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_347_, v_a_348_, v_a_349_);
lean_dec(v_a_349_);
lean_dec_ref(v_a_348_);
lean_dec(v_x_347_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object* v___x_352_, lean_object* v_s_353_, lean_object* v_a_354_, lean_object* v_b_355_){
_start:
{
uint8_t v_decide_356_; 
v_decide_356_ = lean_nat_dec_eq(v_a_354_, v___x_352_);
if (v_decide_356_ == 0)
{
lean_object* v_fst_357_; lean_object* v_snd_358_; uint32_t v___x_359_; lean_object* v___x_360_; uint32_t v___x_361_; uint8_t v___x_362_; 
v_fst_357_ = lean_ctor_get(v_b_355_, 0);
v_snd_358_ = lean_ctor_get(v_b_355_, 1);
v___x_359_ = lean_string_utf8_get_fast(v_s_353_, v_a_354_);
v___x_360_ = lean_string_utf8_next_fast(v_s_353_, v_a_354_);
lean_dec(v_a_354_);
v___x_361_ = 95;
v___x_362_ = lean_uint32_dec_eq(v___x_359_, v___x_361_);
if (v___x_362_ == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_385_; 
lean_inc(v_snd_358_);
lean_inc(v_fst_357_);
v_isSharedCheck_385_ = !lean_is_exclusive(v_b_355_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; lean_object* v_unused_387_; 
v_unused_386_ = lean_ctor_get(v_b_355_, 1);
lean_dec(v_unused_386_);
v_unused_387_ = lean_ctor_get(v_b_355_, 0);
lean_dec(v_unused_387_);
v___x_364_ = v_b_355_;
v_isShared_365_ = v_isSharedCheck_385_;
goto v_resetjp_363_;
}
else
{
lean_dec(v_b_355_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_385_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint32_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = 46;
v___x_367_ = lean_uint32_dec_eq(v___x_359_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; uint32_t v___x_370_; uint32_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_368_ = lean_unsigned_to_nat(10u);
v___x_369_ = lean_nat_mul(v_fst_357_, v___x_368_);
lean_dec(v_fst_357_);
v___x_370_ = 48;
v___x_371_ = lean_uint32_sub(v___x_359_, v___x_370_);
v___x_372_ = lean_uint32_to_nat(v___x_371_);
v___x_373_ = lean_nat_add(v___x_369_, v___x_372_);
lean_dec(v___x_372_);
lean_dec(v___x_369_);
v___x_374_ = lean_unsigned_to_nat(1u);
v___x_375_ = lean_nat_add(v_snd_358_, v___x_374_);
lean_dec(v_snd_358_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v___x_375_);
lean_ctor_set(v___x_364_, 0, v___x_373_);
v___x_377_ = v___x_364_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
v_a_354_ = v___x_360_;
v_b_355_ = v___x_377_;
goto _start;
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_382_; 
lean_dec(v_snd_358_);
v___x_380_ = lean_unsigned_to_nat(0u);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v___x_380_);
v___x_382_ = v___x_364_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_fst_357_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_384_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
v_a_354_ = v___x_360_;
v_b_355_ = v___x_382_;
goto _start;
}
}
}
}
else
{
v_a_354_ = v___x_360_;
goto _start;
}
}
else
{
lean_dec(v_a_354_);
return v_b_355_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object* v___x_389_, lean_object* v_s_390_, lean_object* v_a_391_, lean_object* v_b_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_389_, v_s_390_, v_a_391_, v_b_392_);
lean_dec_ref(v_s_390_);
lean_dec(v___x_389_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object* v_s_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_string_utf8_byte_size(v_s_394_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
lean_inc_ref(v_s_394_);
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v_s_394_);
lean_ctor_set(v___x_398_, 1, v___x_395_);
lean_ctor_set(v___x_398_, 2, v___x_396_);
v___x_399_ = l_String_Slice_positions(v___x_398_);
lean_dec_ref_known(v___x_398_, 3);
v___x_400_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_396_, v_s_394_, v___x_399_, v___x_397_);
v_fst_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_fst_401_);
v_snd_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc(v_snd_402_);
v___x_403_ = lean_string_length(v_s_394_);
lean_dec_ref(v_s_394_);
v___x_404_ = lean_nat_dec_le(v___x_403_, v_snd_402_);
lean_dec(v_snd_402_);
if (v___x_404_ == 0)
{
lean_dec(v_fst_401_);
return v___x_400_;
}
else
{
lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; lean_object* v_unused_413_; 
v_unused_412_ = lean_ctor_get(v___x_400_, 1);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v___x_400_, 0);
lean_dec(v_unused_413_);
v___x_406_ = v___x_400_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_dec(v___x_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_395_);
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_fst_401_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_395_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v_s_416_, lean_object* v_inst_417_, lean_object* v_R_418_, lean_object* v_a_419_, lean_object* v_b_420_, lean_object* v_c_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_415_, v_s_416_, v_a_419_, v_b_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v_s_425_, lean_object* v_inst_426_, lean_object* v_R_427_, lean_object* v_a_428_, lean_object* v_b_429_, lean_object* v_c_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(v___x_423_, v___x_424_, v_s_425_, v_inst_426_, v_R_427_, v_a_428_, v_b_429_, v_c_430_);
lean_dec_ref(v_s_425_);
lean_dec(v___x_424_);
lean_dec_ref(v___x_423_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object* v_s_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0));
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object* v_s_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v_s_436_);
lean_dec_ref(v_s_436_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object* v_s_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v_a_441_, lean_object* v_b_442_){
_start:
{
lean_object* v_it_444_; lean_object* v_startInclusive_445_; lean_object* v_endExclusive_446_; 
if (lean_obj_tag(v_a_441_) == 0)
{
lean_object* v_currPos_451_; lean_object* v_searcher_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_479_; 
v_currPos_451_ = lean_ctor_get(v_a_441_, 0);
v_searcher_452_ = lean_ctor_get(v_a_441_, 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_a_441_);
if (v_isSharedCheck_479_ == 0)
{
v___x_454_ = v_a_441_;
v_isShared_455_ = v_isSharedCheck_479_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_searcher_452_);
lean_inc(v_currPos_451_);
lean_dec(v_a_441_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_479_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v___y_457_; uint8_t v_decide_472_; 
v_decide_472_ = lean_nat_dec_eq(v_searcher_452_, v___x_440_);
if (v_decide_472_ == 0)
{
uint32_t v___x_473_; uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_473_ = lean_string_utf8_get_fast(v_s_438_, v_searcher_452_);
v___x_474_ = 69;
v___x_475_ = lean_uint32_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
uint32_t v___x_476_; uint8_t v___x_477_; 
v___x_476_ = 101;
v___x_477_ = lean_uint32_dec_eq(v___x_473_, v___x_476_);
v___y_457_ = v___x_477_;
goto v___jp_456_;
}
else
{
v___y_457_ = v___x_475_;
goto v___jp_456_;
}
}
else
{
lean_object* v___x_478_; 
lean_del_object(v___x_454_);
lean_dec(v_searcher_452_);
v___x_478_ = lean_box(1);
lean_inc(v___x_440_);
v_it_444_ = v___x_478_;
v_startInclusive_445_ = v_currPos_451_;
v_endExclusive_446_ = v___x_440_;
goto v___jp_443_;
}
v___jp_456_:
{
if (v___y_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = lean_string_utf8_next_fast(v_s_438_, v_searcher_452_);
lean_dec(v_searcher_452_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_458_);
v___x_460_ = v___x_454_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_currPos_451_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_462_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
v_a_441_ = v___x_460_;
goto _start;
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_slice_466_; lean_object* v_nextIt_468_; 
v___x_463_ = lean_string_utf8_next_fast(v_s_438_, v_searcher_452_);
v___x_464_ = lean_nat_sub(v___x_463_, v_searcher_452_);
v___x_465_ = lean_nat_add(v_searcher_452_, v___x_464_);
lean_dec(v___x_464_);
v_slice_466_ = l_String_Slice_subslice_x21(v___x_439_, v_currPos_451_, v_searcher_452_);
lean_inc(v___x_465_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_465_);
lean_ctor_set(v___x_454_, 0, v___x_465_);
v_nextIt_468_ = v___x_454_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_465_);
v_nextIt_468_ = v_reuseFailAlloc_471_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v_startInclusive_469_; lean_object* v_endExclusive_470_; 
v_startInclusive_469_ = lean_ctor_get(v_slice_466_, 0);
lean_inc(v_startInclusive_469_);
v_endExclusive_470_ = lean_ctor_get(v_slice_466_, 1);
lean_inc(v_endExclusive_470_);
lean_dec_ref(v_slice_466_);
v_it_444_ = v_nextIt_468_;
v_startInclusive_445_ = v_startInclusive_469_;
v_endExclusive_446_ = v_endExclusive_470_;
goto v___jp_443_;
}
}
}
}
}
else
{
lean_dec(v___x_440_);
lean_dec_ref(v_s_438_);
return v_b_442_;
}
v___jp_443_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_inc_ref(v_s_438_);
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v_s_438_);
lean_ctor_set(v___x_447_, 1, v_startInclusive_445_);
lean_ctor_set(v___x_447_, 2, v_endExclusive_446_);
v___x_448_ = l_String_Slice_toString(v___x_447_);
lean_dec_ref_known(v___x_447_, 3);
v___x_449_ = lean_array_push(v_b_442_, v___x_448_);
v_a_441_ = v_it_444_;
v_b_442_ = v___x_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object* v_s_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_a_483_, lean_object* v_b_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_480_, v___x_481_, v___x_482_, v_a_483_, v_b_484_);
lean_dec_ref(v___x_481_);
return v_res_485_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_nat_to_int(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object* v_s_493_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_string_utf8_byte_size(v_s_493_);
lean_inc_ref(v_s_493_);
v___x_498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_498_, 0, v_s_493_);
lean_ctor_set(v___x_498_, 1, v___x_496_);
lean_ctor_set(v___x_498_, 2, v___x_497_);
v___x_499_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v___x_498_);
v___x_500_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2));
v___x_501_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_493_, v___x_498_, v___x_497_, v___x_499_, v___x_500_);
lean_dec_ref_known(v___x_498_, 3);
v___x_502_ = lean_array_to_list(v___x_501_);
if (lean_obj_tag(v___x_502_) == 1)
{
lean_object* v_tail_503_; 
v_tail_503_ = lean_ctor_get(v___x_502_, 1);
lean_inc(v_tail_503_);
if (lean_obj_tag(v_tail_503_) == 0)
{
lean_object* v_head_504_; lean_object* v___x_505_; lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
v_head_504_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_head_504_);
lean_dec_ref_known(v___x_502_, 2);
v___x_505_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_504_);
v_fst_506_ = lean_ctor_get(v___x_505_, 0);
v_snd_507_ = lean_ctor_get(v___x_505_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_515_ == 0)
{
v___x_509_ = v___x_505_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_inc(v_fst_506_);
lean_dec(v___x_505_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = l_Int_negOfNat(v_snd_507_);
lean_dec(v_snd_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_fst_506_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
else
{
lean_object* v_tail_516_; 
v_tail_516_ = lean_ctor_get(v_tail_503_, 1);
if (lean_obj_tag(v_tail_516_) == 0)
{
lean_object* v_head_517_; lean_object* v_head_518_; lean_object* v___x_519_; lean_object* v_fst_520_; lean_object* v_snd_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_531_; 
v_head_517_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_head_517_);
lean_dec_ref_known(v___x_502_, 2);
v_head_518_ = lean_ctor_get(v_tail_503_, 0);
lean_inc(v_head_518_);
lean_dec_ref_known(v_tail_503_, 2);
v___x_519_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_517_);
v_fst_520_ = lean_ctor_get(v___x_519_, 0);
v_snd_521_ = lean_ctor_get(v___x_519_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_531_ == 0)
{
v___x_523_ = v___x_519_;
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_snd_521_);
lean_inc(v_fst_520_);
lean_dec(v___x_519_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_531_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_exp_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v_exp_525_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_head_518_);
v___x_526_ = l_Int_negOfNat(v_snd_521_);
lean_dec(v_snd_521_);
v___x_527_ = lean_int_add(v___x_526_, v_exp_525_);
lean_dec(v_exp_525_);
lean_dec(v___x_526_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v___x_527_);
v___x_529_ = v___x_523_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fst_520_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
lean_dec_ref_known(v_tail_503_, 2);
lean_dec_ref_known(v___x_502_, 2);
goto v___jp_494_;
}
}
}
else
{
lean_dec(v___x_502_);
goto v___jp_494_;
}
v___jp_494_:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object* v_s_532_, lean_object* v___x_533_, lean_object* v___x_534_, lean_object* v_inst_535_, lean_object* v_R_536_, lean_object* v_a_537_, lean_object* v_b_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_532_, v___x_533_, v___x_534_, v_a_537_, v_b_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object* v_s_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v_inst_543_, lean_object* v_R_544_, lean_object* v_a_545_, lean_object* v_b_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(v_s_540_, v___x_541_, v___x_542_, v_inst_543_, v_R_544_, v_a_545_, v_b_546_);
lean_dec_ref(v___x_541_);
return v_res_547_;
}
}
static double _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2(void){
_start:
{
lean_object* v___x_550_; double v___x_551_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_float_of_nat(v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object* v_s_552_){
_start:
{
lean_object* v___x_553_; lean_object* v_fst_554_; lean_object* v_snd_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_553_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(v_s_552_);
v_fst_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc(v_fst_554_);
v_snd_555_ = lean_ctor_get(v___x_553_, 1);
lean_inc(v_snd_555_);
lean_dec_ref(v___x_553_);
v___x_556_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0));
v___x_557_ = lean_string_dec_eq(v_snd_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1));
v___x_559_ = lean_string_dec_eq(v_snd_555_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v_fst_561_; lean_object* v_snd_562_; lean_object* v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; double v_flt_566_; uint8_t v___x_567_; 
v___x_560_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(v_snd_555_);
v_fst_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_fst_561_);
v_snd_562_ = lean_ctor_get(v___x_560_, 1);
lean_inc(v_snd_562_);
lean_dec_ref(v___x_560_);
v___x_563_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_564_ = lean_int_dec_lt(v_snd_562_, v___x_563_);
v___x_565_ = lean_nat_abs(v_snd_562_);
lean_dec(v_snd_562_);
v_flt_566_ = l_Float_ofScientific(v_fst_561_, v___x_564_, v___x_565_);
v___x_567_ = lean_unbox(v_fst_554_);
lean_dec(v_fst_554_);
if (v___x_567_ == 0)
{
return v_flt_566_;
}
else
{
double v___x_568_; 
v___x_568_ = lean_float_negate(v_flt_566_);
return v___x_568_;
}
}
else
{
uint8_t v___x_569_; 
lean_dec(v_snd_555_);
v___x_569_ = lean_unbox(v_fst_554_);
lean_dec(v_fst_554_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; double v___x_572_; double v___x_573_; double v___x_574_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = l_Float_ofScientific(v___x_570_, v___x_559_, v___x_571_);
v___x_573_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_574_ = lean_float_div(v___x_572_, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; double v___x_577_; double v___x_578_; double v___x_579_; double v___x_580_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = l_Float_ofScientific(v___x_575_, v___x_559_, v___x_576_);
v___x_578_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_579_ = lean_float_div(v___x_577_, v___x_578_);
v___x_580_ = lean_float_negate(v___x_579_);
return v___x_580_;
}
}
}
else
{
uint8_t v___x_581_; 
lean_dec(v_snd_555_);
v___x_581_ = lean_unbox(v_fst_554_);
lean_dec(v_fst_554_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; double v___x_584_; double v___x_585_; double v___x_586_; 
v___x_582_ = lean_unsigned_to_nat(10u);
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = l_Float_ofScientific(v___x_582_, v___x_557_, v___x_583_);
v___x_585_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_586_ = lean_float_div(v___x_584_, v___x_585_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; double v___x_589_; double v___x_590_; double v___x_591_; double v___x_592_; 
v___x_587_ = lean_unsigned_to_nat(10u);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = l_Float_ofScientific(v___x_587_, v___x_557_, v___x_588_);
v___x_590_ = lean_float_negate(v___x_589_);
v___x_591_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_592_ = lean_float_div(v___x_590_, v___x_591_);
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object* v_s_593_){
_start:
{
double v_res_594_; lean_object* v_r_595_; 
v_res_594_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_s_593_);
v_r_595_ = lean_box_float(v_res_594_);
return v_r_595_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3));
v___x_605_ = l_Lean_MessageData_ofFormat(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object* v_x_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_a_611_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
v___x_616_ = l_Lean_Syntax_isLit_x3f(v___x_615_, v_x_606_);
if (lean_obj_tag(v___x_616_) == 1)
{
lean_object* v_val_617_; 
v_val_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v___x_616_, 1);
v_a_611_ = v_val_617_;
goto v___jp_610_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v___x_616_);
v___x_618_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4);
v___x_619_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_606_, v___x_618_, v_a_607_, v_a_608_);
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
v___jp_610_:
{
double v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_a_611_);
v___x_613_ = lean_box_float(v___x_612_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object* v_x_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_x_628_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_b_637_){
_start:
{
lean_object* v___x_638_; uint8_t v_decide_639_; 
v___x_638_ = lean_nat_sub(v___x_633_, v___x_634_);
v_decide_639_ = lean_nat_dec_eq(v_a_636_, v___x_638_);
lean_dec(v___x_638_);
if (v_decide_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint32_t v___x_643_; uint32_t v___x_644_; uint8_t v___x_645_; 
v___x_640_ = lean_nat_add(v___x_634_, v_a_636_);
lean_dec(v_a_636_);
v___x_641_ = lean_string_utf8_next_fast(v_a_635_, v___x_640_);
v___x_642_ = lean_nat_sub(v___x_641_, v___x_634_);
v___x_643_ = lean_string_utf8_get_fast(v_a_635_, v___x_640_);
lean_dec(v___x_640_);
v___x_644_ = 95;
v___x_645_ = lean_uint32_dec_eq(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; uint32_t v___x_648_; uint32_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_646_ = lean_unsigned_to_nat(2u);
v___x_647_ = lean_nat_mul(v_b_637_, v___x_646_);
lean_dec(v_b_637_);
v___x_648_ = 48;
v___x_649_ = lean_uint32_sub(v___x_643_, v___x_648_);
v___x_650_ = lean_uint32_to_nat(v___x_649_);
v___x_651_ = lean_nat_add(v___x_647_, v___x_650_);
lean_dec(v___x_650_);
lean_dec(v___x_647_);
v_a_636_ = v___x_642_;
v_b_637_ = v___x_651_;
goto _start;
}
else
{
v_a_636_ = v___x_642_;
goto _start;
}
}
else
{
lean_dec(v_a_636_);
return v_b_637_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object* v___x_654_, lean_object* v___x_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_b_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_654_, v___x_655_, v_a_656_, v_a_657_, v_b_658_);
lean_dec_ref(v_a_656_);
lean_dec(v___x_655_);
lean_dec(v___x_654_);
return v_res_659_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3));
v___x_669_ = l_Lean_MessageData_ofFormat(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object* v_x_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_a_675_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
v___x_686_ = l_Lean_Syntax_isLit_x3f(v___x_685_, v_x_670_);
if (lean_obj_tag(v___x_686_) == 1)
{
lean_object* v_val_687_; 
v_val_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v___x_686_, 1);
v_a_675_ = v_val_687_;
goto v___jp_674_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v___x_686_);
v___x_688_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4);
v___x_689_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_670_, v___x_688_, v_a_671_, v_a_672_);
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_unsigned_to_nat(2u);
v___x_678_ = lean_string_utf8_byte_size(v_a_675_);
lean_inc_ref_n(v_a_675_, 2);
v___x_679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_679_, 0, v_a_675_);
lean_ctor_set(v___x_679_, 1, v___x_676_);
lean_ctor_set(v___x_679_, 2, v___x_678_);
v___x_680_ = l_String_Slice_Pos_nextn(v___x_679_, v___x_676_, v___x_677_);
lean_dec_ref_known(v___x_679_, 3);
lean_inc(v___x_680_);
v___x_681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_681_, 0, v_a_675_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_ctor_set(v___x_681_, 2, v___x_678_);
v___x_682_ = l_String_Slice_positions(v___x_681_);
lean_dec_ref_known(v___x_681_, 3);
v___x_683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_678_, v___x_680_, v_a_675_, v___x_682_, v___x_676_);
lean_dec_ref(v_a_675_);
lean_dec(v___x_680_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object* v_x_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_x_698_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object* v___x_703_, lean_object* v___x_704_, lean_object* v___x_705_, lean_object* v_a_706_, lean_object* v_inst_707_, lean_object* v_R_708_, lean_object* v_a_709_, lean_object* v_b_710_, lean_object* v_c_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_703_, v___x_704_, v_a_706_, v_a_709_, v_b_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object* v___x_713_, lean_object* v___x_714_, lean_object* v___x_715_, lean_object* v_a_716_, lean_object* v_inst_717_, lean_object* v_R_718_, lean_object* v_a_719_, lean_object* v_b_720_, lean_object* v_c_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(v___x_713_, v___x_714_, v___x_715_, v_a_716_, v_inst_717_, v_R_718_, v_a_719_, v_b_720_, v_c_721_);
lean_dec_ref(v_a_716_);
lean_dec_ref(v___x_715_);
lean_dec(v___x_714_);
lean_dec(v___x_713_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object* v___x_723_, lean_object* v___x_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_b_727_){
_start:
{
lean_object* v___x_728_; uint8_t v_decide_729_; 
v___x_728_ = lean_nat_sub(v___x_723_, v___x_724_);
v_decide_729_ = lean_nat_dec_eq(v_a_726_, v___x_728_);
lean_dec(v___x_728_);
if (v_decide_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint32_t v___x_733_; uint32_t v___x_734_; uint8_t v___x_735_; 
v___x_730_ = lean_nat_add(v___x_724_, v_a_726_);
lean_dec(v_a_726_);
v___x_731_ = lean_string_utf8_next_fast(v_a_725_, v___x_730_);
v___x_732_ = lean_nat_sub(v___x_731_, v___x_724_);
v___x_733_ = lean_string_utf8_get_fast(v_a_725_, v___x_730_);
lean_dec(v___x_730_);
v___x_734_ = 95;
v___x_735_ = lean_uint32_dec_eq(v___x_733_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; uint32_t v___x_738_; uint32_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_736_ = lean_unsigned_to_nat(8u);
v___x_737_ = lean_nat_mul(v_b_727_, v___x_736_);
lean_dec(v_b_727_);
v___x_738_ = 48;
v___x_739_ = lean_uint32_sub(v___x_733_, v___x_738_);
v___x_740_ = lean_uint32_to_nat(v___x_739_);
v___x_741_ = lean_nat_add(v___x_737_, v___x_740_);
lean_dec(v___x_740_);
lean_dec(v___x_737_);
v_a_726_ = v___x_732_;
v_b_727_ = v___x_741_;
goto _start;
}
else
{
v_a_726_ = v___x_732_;
goto _start;
}
}
else
{
lean_dec(v_a_726_);
return v_b_727_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object* v___x_744_, lean_object* v___x_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_b_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_744_, v___x_745_, v_a_746_, v_a_747_, v_b_748_);
lean_dec_ref(v_a_746_);
lean_dec(v___x_745_);
lean_dec(v___x_744_);
return v_res_749_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3));
v___x_759_ = l_Lean_MessageData_ofFormat(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object* v_x_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_a_765_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
v___x_776_ = l_Lean_Syntax_isLit_x3f(v___x_775_, v_x_760_);
if (lean_obj_tag(v___x_776_) == 1)
{
lean_object* v_val_777_; 
v_val_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_val_777_);
lean_dec_ref_known(v___x_776_, 1);
v_a_765_ = v_val_777_;
goto v___jp_764_;
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec(v___x_776_);
v___x_778_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4);
v___x_779_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_760_, v___x_778_, v_a_761_, v_a_762_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
v___jp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_unsigned_to_nat(2u);
v___x_768_ = lean_string_utf8_byte_size(v_a_765_);
lean_inc_ref_n(v_a_765_, 2);
v___x_769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_769_, 0, v_a_765_);
lean_ctor_set(v___x_769_, 1, v___x_766_);
lean_ctor_set(v___x_769_, 2, v___x_768_);
v___x_770_ = l_String_Slice_Pos_nextn(v___x_769_, v___x_766_, v___x_767_);
lean_dec_ref_known(v___x_769_, 3);
lean_inc(v___x_770_);
v___x_771_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_771_, 0, v_a_765_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
lean_ctor_set(v___x_771_, 2, v___x_768_);
v___x_772_ = l_String_Slice_positions(v___x_771_);
lean_dec_ref_known(v___x_771_, 3);
v___x_773_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_768_, v___x_770_, v_a_765_, v___x_772_, v___x_766_);
lean_dec_ref(v_a_765_);
lean_dec(v___x_770_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object* v_x_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_788_, v_a_789_, v_a_790_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_x_788_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object* v___x_793_, lean_object* v___x_794_, lean_object* v___x_795_, lean_object* v_a_796_, lean_object* v_inst_797_, lean_object* v_R_798_, lean_object* v_a_799_, lean_object* v_b_800_, lean_object* v_c_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_793_, v___x_794_, v_a_796_, v_a_799_, v_b_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object* v___x_803_, lean_object* v___x_804_, lean_object* v___x_805_, lean_object* v_a_806_, lean_object* v_inst_807_, lean_object* v_R_808_, lean_object* v_a_809_, lean_object* v_b_810_, lean_object* v_c_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(v___x_803_, v___x_804_, v___x_805_, v_a_806_, v_inst_807_, v_R_808_, v_a_809_, v_b_810_, v_c_811_);
lean_dec_ref(v_a_806_);
lean_dec_ref(v___x_805_);
lean_dec(v___x_804_);
lean_dec(v___x_803_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t v_c_813_){
_start:
{
uint32_t v___x_814_; uint8_t v___x_815_; 
v___x_814_ = 57;
v___x_815_ = lean_uint32_dec_le(v_c_813_, v___x_814_);
if (v___x_815_ == 0)
{
uint32_t v___x_816_; uint8_t v___x_817_; 
v___x_816_ = 70;
v___x_817_ = lean_uint32_dec_le(v_c_813_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; uint32_t v___x_819_; uint32_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_818_ = lean_unsigned_to_nat(10u);
v___x_819_ = 97;
v___x_820_ = lean_uint32_sub(v_c_813_, v___x_819_);
v___x_821_ = lean_uint32_to_nat(v___x_820_);
v___x_822_ = lean_nat_add(v___x_818_, v___x_821_);
lean_dec(v___x_821_);
return v___x_822_;
}
else
{
lean_object* v___x_823_; uint32_t v___x_824_; uint32_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_823_ = lean_unsigned_to_nat(10u);
v___x_824_ = 65;
v___x_825_ = lean_uint32_sub(v_c_813_, v___x_824_);
v___x_826_ = lean_uint32_to_nat(v___x_825_);
v___x_827_ = lean_nat_add(v___x_823_, v___x_826_);
lean_dec(v___x_826_);
return v___x_827_;
}
}
else
{
uint32_t v___x_828_; uint32_t v___x_829_; lean_object* v___x_830_; 
v___x_828_ = 48;
v___x_829_ = lean_uint32_sub(v_c_813_, v___x_828_);
v___x_830_ = lean_uint32_to_nat(v___x_829_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object* v_c_831_){
_start:
{
uint32_t v_c_boxed_832_; lean_object* v_res_833_; 
v_c_boxed_832_ = lean_unbox_uint32(v_c_831_);
lean_dec(v_c_831_);
v_res_833_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v_c_boxed_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object* v___x_834_, lean_object* v___x_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_b_838_){
_start:
{
lean_object* v___x_839_; uint8_t v_decide_840_; 
v___x_839_ = lean_nat_sub(v___x_834_, v___x_835_);
v_decide_840_ = lean_nat_dec_eq(v_a_837_, v___x_839_);
lean_dec(v___x_839_);
if (v_decide_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint32_t v___x_844_; uint32_t v___x_845_; uint8_t v___x_846_; 
v___x_841_ = lean_nat_add(v___x_835_, v_a_837_);
lean_dec(v_a_837_);
v___x_842_ = lean_string_utf8_next_fast(v_a_836_, v___x_841_);
v___x_843_ = lean_nat_sub(v___x_842_, v___x_835_);
v___x_844_ = lean_string_utf8_get_fast(v_a_836_, v___x_841_);
lean_dec(v___x_841_);
v___x_845_ = 95;
v___x_846_ = lean_uint32_dec_eq(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_847_ = lean_unsigned_to_nat(16u);
v___x_848_ = lean_nat_mul(v_b_838_, v___x_847_);
lean_dec(v_b_838_);
v___x_849_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_844_);
v___x_850_ = lean_nat_add(v___x_848_, v___x_849_);
lean_dec(v___x_849_);
lean_dec(v___x_848_);
v_a_837_ = v___x_843_;
v_b_838_ = v___x_850_;
goto _start;
}
else
{
v_a_837_ = v___x_843_;
goto _start;
}
}
else
{
lean_dec(v_a_837_);
return v_b_838_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object* v___x_853_, lean_object* v___x_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_b_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_853_, v___x_854_, v_a_855_, v_a_856_, v_b_857_);
lean_dec_ref(v_a_855_);
lean_dec(v___x_854_);
lean_dec(v___x_853_);
return v_res_858_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3));
v___x_868_ = l_Lean_MessageData_ofFormat(v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object* v_x_869_, lean_object* v_a_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_a_874_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
v___x_885_ = l_Lean_Syntax_isLit_x3f(v___x_884_, v_x_869_);
if (lean_obj_tag(v___x_885_) == 1)
{
lean_object* v_val_886_; 
v_val_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_val_886_);
lean_dec_ref_known(v___x_885_, 1);
v_a_874_ = v_val_886_;
goto v___jp_873_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec(v___x_885_);
v___x_887_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4);
v___x_888_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_869_, v___x_887_, v_a_870_, v_a_871_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
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
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
v___jp_873_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = lean_unsigned_to_nat(2u);
v___x_877_ = lean_string_utf8_byte_size(v_a_874_);
lean_inc_ref_n(v_a_874_, 2);
v___x_878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_878_, 0, v_a_874_);
lean_ctor_set(v___x_878_, 1, v___x_875_);
lean_ctor_set(v___x_878_, 2, v___x_877_);
v___x_879_ = l_String_Slice_Pos_nextn(v___x_878_, v___x_875_, v___x_876_);
lean_dec_ref_known(v___x_878_, 3);
lean_inc(v___x_879_);
v___x_880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_880_, 0, v_a_874_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
lean_ctor_set(v___x_880_, 2, v___x_877_);
v___x_881_ = l_String_Slice_positions(v___x_880_);
lean_dec_ref_known(v___x_880_, 3);
v___x_882_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_877_, v___x_879_, v_a_874_, v___x_881_, v___x_875_);
lean_dec_ref(v_a_874_);
lean_dec(v___x_879_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object* v_x_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_x_897_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v_a_905_, lean_object* v_inst_906_, lean_object* v_R_907_, lean_object* v_a_908_, lean_object* v_b_909_, lean_object* v_c_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_902_, v___x_903_, v_a_905_, v_a_908_, v_b_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_a_915_, lean_object* v_inst_916_, lean_object* v_R_917_, lean_object* v_a_918_, lean_object* v_b_919_, lean_object* v_c_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(v___x_912_, v___x_913_, v___x_914_, v_a_915_, v_inst_916_, v_R_917_, v_a_918_, v_b_919_, v_c_920_);
lean_dec_ref(v_a_915_);
lean_dec_ref(v___x_914_);
lean_dec(v___x_913_);
lean_dec(v___x_912_);
return v_res_921_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5));
v___x_934_ = l_Lean_MessageData_ofFormat(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object* v_x_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_a_940_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
v___x_953_ = l_Lean_Syntax_isLit_x3f(v___x_952_, v_x_935_);
if (lean_obj_tag(v___x_953_) == 1)
{
lean_object* v_val_954_; 
v_val_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_val_954_);
lean_dec_ref_known(v___x_953_, 1);
v_a_940_ = v_val_954_;
goto v___jp_939_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_dec(v___x_953_);
v___x_955_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6);
v___x_956_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_935_, v___x_955_, v_a_936_, v_a_937_);
v_a_957_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_956_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_956_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
v___jp_939_:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lake_Toml_DateTime_ofString_x3f(v_a_940_);
if (lean_obj_tag(v___x_941_) == 1)
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_val_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 0);
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_val_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v___x_941_);
v___x_950_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1);
v___x_951_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_935_, v___x_950_, v_a_936_, v_a_937_);
return v___x_951_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object* v_x_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_x_965_);
return v_res_969_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3));
v___x_979_ = l_Lean_MessageData_ofFormat(v___x_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object* v_x_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_a_985_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
v___x_998_ = l_Lean_Syntax_isLit_x3f(v___x_997_, v_x_980_);
if (lean_obj_tag(v___x_998_) == 1)
{
lean_object* v_val_999_; 
v_val_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_val_999_);
lean_dec_ref_known(v___x_998_, 1);
v_a_985_ = v_val_999_;
goto v___jp_984_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
lean_dec(v___x_998_);
v___x_1000_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4);
v___x_1001_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_980_, v___x_1000_, v_a_981_, v_a_982_);
return v___x_1001_;
}
v___jp_984_:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_string_utf8_byte_size(v_a_985_);
lean_inc_ref_n(v_a_985_, 2);
v___x_989_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_989_, 0, v_a_985_);
lean_ctor_set(v___x_989_, 1, v___x_987_);
lean_ctor_set(v___x_989_, 2, v___x_988_);
v___x_990_ = l_String_Slice_Pos_nextn(v___x_989_, v___x_987_, v___x_986_);
lean_dec_ref_known(v___x_989_, 3);
lean_inc(v___x_990_);
v___x_991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_991_, 0, v_a_985_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
lean_ctor_set(v___x_991_, 2, v___x_988_);
v___x_992_ = lean_nat_sub(v___x_988_, v___x_990_);
v___x_993_ = l_String_Slice_Pos_prevn(v___x_991_, v___x_992_, v___x_986_);
lean_dec_ref_known(v___x_991_, 3);
v___x_994_ = lean_nat_add(v___x_990_, v___x_993_);
lean_dec(v___x_993_);
v___x_995_ = lean_string_utf8_extract_fast(v_a_985_, v___x_990_, v___x_994_);
lean_dec(v___x_994_);
lean_dec(v___x_990_);
lean_dec_ref(v_a_985_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object* v_x_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_x_1002_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object* v_msg_1007_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = l_String_instInhabitedSlice;
v___x_1009_ = lean_panic_fn_borrowed(v___x_1008_, v_msg_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object* v___y_1010_, lean_object* v_a_1011_, lean_object* v_b_1012_){
_start:
{
lean_object* v_str_1013_; lean_object* v_startInclusive_1014_; lean_object* v_endExclusive_1015_; lean_object* v___x_1016_; uint8_t v_decide_1017_; 
v_str_1013_ = lean_ctor_get(v___y_1010_, 0);
v_startInclusive_1014_ = lean_ctor_get(v___y_1010_, 1);
v_endExclusive_1015_ = lean_ctor_get(v___y_1010_, 2);
v___x_1016_ = lean_nat_sub(v_endExclusive_1015_, v_startInclusive_1014_);
v_decide_1017_ = lean_nat_dec_eq(v_a_1011_, v___x_1016_);
lean_dec(v___x_1016_);
if (v_decide_1017_ == 0)
{
lean_object* v___x_1018_; uint32_t v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1018_ = lean_nat_add(v_startInclusive_1014_, v_a_1011_);
lean_dec(v_a_1011_);
v___x_1019_ = lean_string_utf8_get_fast(v_str_1013_, v___x_1018_);
v___x_1020_ = lean_string_utf8_next_fast(v_str_1013_, v___x_1018_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_nat_sub(v___x_1020_, v_startInclusive_1014_);
v___x_1022_ = lean_unsigned_to_nat(16u);
v___x_1023_ = lean_nat_mul(v_b_1012_, v___x_1022_);
lean_dec(v_b_1012_);
v___x_1024_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_1019_);
v___x_1025_ = lean_nat_add(v___x_1023_, v___x_1024_);
lean_dec(v___x_1024_);
lean_dec(v___x_1023_);
v_a_1011_ = v___x_1021_;
v_b_1012_ = v___x_1025_;
goto _start;
}
else
{
lean_dec(v_a_1011_);
return v_b_1012_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object* v___y_1027_, lean_object* v_a_1028_, lean_object* v_b_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1027_, v_a_1028_, v_b_1029_);
lean_dec_ref(v___y_1027_);
return v_res_1030_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1034_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2));
v___x_1035_ = lean_unsigned_to_nat(14u);
v___x_1036_ = lean_unsigned_to_nat(22u);
v___x_1037_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1));
v___x_1038_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0));
v___x_1039_ = l_mkPanicMessageWithDecl(v___x_1038_, v___x_1037_, v___x_1036_, v___x_1035_, v___x_1034_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object* v_s_1040_){
_start:
{
lean_object* v_str_1041_; lean_object* v_startPos_1042_; lean_object* v_stopPos_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1064_; 
v_str_1041_ = lean_ctor_get(v_s_1040_, 0);
v_startPos_1042_ = lean_ctor_get(v_s_1040_, 1);
v_stopPos_1043_ = lean_ctor_get(v_s_1040_, 2);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_s_1040_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1045_ = v_s_1040_;
v_isShared_1046_ = v_isSharedCheck_1064_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_stopPos_1043_);
lean_inc(v_startPos_1042_);
lean_inc(v_str_1041_);
lean_dec(v_s_1040_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1064_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___y_1049_; uint8_t v___y_1053_; uint8_t v___x_1059_; uint8_t v___y_1061_; uint8_t v___x_1062_; 
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1059_ = lean_string_is_valid_pos(v_str_1041_, v_startPos_1042_);
v___x_1062_ = lean_string_is_valid_pos(v_str_1041_, v_stopPos_1043_);
if (v___x_1062_ == 0)
{
v___y_1061_ = v___x_1062_;
goto v___jp_1060_;
}
else
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_nat_dec_le(v_startPos_1042_, v_stopPos_1043_);
v___y_1061_ = v___x_1063_;
goto v___jp_1060_;
}
v___jp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = l_String_Slice_positions(v___y_1049_);
v___x_1051_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1049_, v___x_1050_, v___x_1047_);
lean_dec_ref(v___y_1049_);
return v___x_1051_;
}
v___jp_1052_:
{
if (v___y_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_del_object(v___x_1045_);
lean_dec(v_stopPos_1043_);
lean_dec(v_startPos_1042_);
lean_dec_ref(v_str_1041_);
v___x_1054_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3);
v___x_1055_ = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(v___x_1054_);
v___y_1049_ = v___x_1055_;
goto v___jp_1048_;
}
else
{
lean_object* v___x_1057_; 
if (v_isShared_1046_ == 0)
{
v___x_1057_ = v___x_1045_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_str_1041_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_startPos_1042_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_stopPos_1043_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
v___y_1049_ = v___x_1057_;
goto v___jp_1048_;
}
}
}
v___jp_1060_:
{
if (v___x_1059_ == 0)
{
v___y_1053_ = v___x_1059_;
goto v___jp_1052_;
}
else
{
v___y_1053_ = v___y_1061_;
goto v___jp_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object* v___y_1065_, lean_object* v_inst_1066_, lean_object* v_R_1067_, lean_object* v_a_1068_, lean_object* v_b_1069_, lean_object* v_c_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1065_, v_a_1068_, v_b_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object* v___y_1072_, lean_object* v_inst_1073_, lean_object* v_R_1074_, lean_object* v_a_1075_, lean_object* v_b_1076_, lean_object* v_c_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(v___y_1072_, v_inst_1073_, v_R_1074_, v_a_1075_, v_b_1076_, v_c_1077_);
lean_dec_ref(v___y_1072_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object* v_s_1079_, lean_object* v_stopPos_1080_, lean_object* v_i_1081_){
_start:
{
uint8_t v___y_1083_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_add(v_i_1081_, v___x_1086_);
v___x_1088_ = lean_nat_dec_le(v___x_1087_, v_stopPos_1080_);
lean_dec(v___x_1087_);
if (v___x_1088_ == 0)
{
return v_i_1081_;
}
else
{
if (v___x_1088_ == 0)
{
v___y_1083_ = v___x_1088_;
goto v___jp_1082_;
}
else
{
uint32_t v___x_1089_; uint32_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1089_ = lean_string_utf8_get(v_s_1079_, v_i_1081_);
v___x_1090_ = 32;
v___x_1091_ = lean_uint32_dec_eq(v___x_1089_, v___x_1090_);
if (v___x_1091_ == 0)
{
uint32_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = 9;
v___x_1093_ = lean_uint32_dec_eq(v___x_1089_, v___x_1092_);
if (v___x_1093_ == 0)
{
uint32_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = 13;
v___x_1095_ = lean_uint32_dec_eq(v___x_1089_, v___x_1094_);
if (v___x_1095_ == 0)
{
uint32_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = 10;
v___x_1097_ = lean_uint32_dec_eq(v___x_1089_, v___x_1096_);
v___y_1083_ = v___x_1097_;
goto v___jp_1082_;
}
else
{
v___y_1083_ = v___x_1095_;
goto v___jp_1082_;
}
}
else
{
v___y_1083_ = v___x_1093_;
goto v___jp_1082_;
}
}
else
{
v___y_1083_ = v___x_1091_;
goto v___jp_1082_;
}
}
}
v___jp_1082_:
{
if (v___y_1083_ == 0)
{
return v_i_1081_;
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_string_utf8_next(v_s_1079_, v_i_1081_);
lean_dec(v_i_1081_);
v_i_1081_ = v___x_1084_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object* v_s_1098_, lean_object* v_stopPos_1099_, lean_object* v_i_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_s_1098_, v_stopPos_1099_, v_i_1100_);
lean_dec(v_stopPos_1099_);
lean_dec_ref(v_s_1098_);
return v_res_1101_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object* v_lit_1108_, lean_object* v_i_1109_, lean_object* v_out_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1124_; uint8_t v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; uint8_t v___y_1129_; lean_object* v_escape_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; uint8_t v___x_1149_; 
v___x_1149_ = lean_string_utf8_at_end(v_lit_1108_, v_i_1109_);
if (v___x_1149_ == 0)
{
uint32_t v_curr_1150_; lean_object* v_i_1151_; uint32_t v___x_1152_; uint8_t v___x_1153_; 
v_curr_1150_ = lean_string_utf8_get_fast(v_lit_1108_, v_i_1109_);
v_i_1151_ = lean_string_utf8_next_fast(v_lit_1108_, v_i_1109_);
lean_dec(v_i_1109_);
v___x_1152_ = 92;
v___x_1153_ = lean_uint32_dec_eq(v_curr_1150_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_string_push(v_out_1110_, v_curr_1150_);
v_i_1109_ = v_i_1151_;
v_out_1110_ = v___x_1154_;
goto _start;
}
else
{
uint8_t v___x_1156_; 
v___x_1156_ = lean_string_utf8_at_end(v_lit_1108_, v_i_1151_);
if (v___x_1156_ == 0)
{
uint32_t v_curr_1157_; lean_object* v_next_1158_; uint32_t v___x_1159_; uint8_t v___x_1160_; 
v_curr_1157_ = lean_string_utf8_get_fast(v_lit_1108_, v_i_1151_);
v_next_1158_ = lean_string_utf8_next_fast(v_lit_1108_, v_i_1151_);
v___x_1159_ = 98;
v___x_1160_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 116;
v___x_1162_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 110;
v___x_1164_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 102;
v___x_1166_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 114;
v___x_1168_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint32_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = 34;
v___x_1170_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1169_);
if (v___x_1170_ == 0)
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1152_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 117;
v___x_1173_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = 85;
v___x_1175_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v_b_1177_; 
v___x_1176_ = lean_string_utf8_byte_size(v_lit_1108_);
v_b_1177_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_lit_1108_, v___x_1176_, v_i_1151_);
v_i_1109_ = v_b_1177_;
goto _start;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1179_ = lean_string_utf8_byte_size(v_lit_1108_);
lean_inc_ref_n(v_lit_1108_, 2);
v___x_1180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1180_, 0, v_lit_1108_);
lean_ctor_set(v___x_1180_, 1, v_next_1158_);
lean_ctor_set(v___x_1180_, 2, v___x_1179_);
v___x_1181_ = lean_unsigned_to_nat(8u);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = l_Substring_Raw_nextn(v___x_1180_, v___x_1181_, v___x_1182_);
lean_dec_ref_known(v___x_1180_, 3);
v___x_1184_ = lean_nat_add(v_next_1158_, v___x_1183_);
lean_dec(v___x_1183_);
v___x_1185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1185_, 0, v_lit_1108_);
lean_ctor_set(v___x_1185_, 1, v_next_1158_);
lean_ctor_set(v___x_1185_, 2, v___x_1184_);
v_escape_1139_ = v___x_1185_;
v___y_1140_ = v_a_1111_;
v___y_1141_ = v_a_1112_;
goto v___jp_1138_;
}
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1186_ = lean_string_utf8_byte_size(v_lit_1108_);
lean_inc_ref_n(v_lit_1108_, 2);
v___x_1187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1187_, 0, v_lit_1108_);
lean_ctor_set(v___x_1187_, 1, v_next_1158_);
lean_ctor_set(v___x_1187_, 2, v___x_1186_);
v___x_1188_ = lean_unsigned_to_nat(4u);
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = l_Substring_Raw_nextn(v___x_1187_, v___x_1188_, v___x_1189_);
lean_dec_ref_known(v___x_1187_, 3);
v___x_1191_ = lean_nat_add(v_next_1158_, v___x_1190_);
lean_dec(v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1192_, 0, v_lit_1108_);
lean_ctor_set(v___x_1192_, 1, v_next_1158_);
lean_ctor_set(v___x_1192_, 2, v___x_1191_);
v_escape_1139_ = v___x_1192_;
v___y_1140_ = v_a_1111_;
v___y_1141_ = v_a_1112_;
goto v___jp_1138_;
}
}
else
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_string_push(v_out_1110_, v___x_1152_);
v_i_1109_ = v_next_1158_;
v_out_1110_ = v___x_1193_;
goto _start;
}
}
else
{
lean_object* v___x_1195_; 
v___x_1195_ = lean_string_push(v_out_1110_, v___x_1169_);
v_i_1109_ = v_next_1158_;
v_out_1110_ = v___x_1195_;
goto _start;
}
}
else
{
uint32_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = 13;
v___x_1198_ = lean_string_push(v_out_1110_, v___x_1197_);
v_i_1109_ = v_next_1158_;
v_out_1110_ = v___x_1198_;
goto _start;
}
}
else
{
uint32_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = 12;
v___x_1201_ = lean_string_push(v_out_1110_, v___x_1200_);
v_i_1109_ = v_next_1158_;
v_out_1110_ = v___x_1201_;
goto _start;
}
}
else
{
uint32_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = 10;
v___x_1204_ = lean_string_push(v_out_1110_, v___x_1203_);
v_i_1109_ = v_next_1158_;
v_out_1110_ = v___x_1204_;
goto _start;
}
}
else
{
uint32_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = 9;
v___x_1207_ = lean_string_push(v_out_1110_, v___x_1206_);
v_i_1109_ = v_next_1158_;
v_out_1110_ = v___x_1207_;
goto _start;
}
}
else
{
uint32_t v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = 8;
v___x_1210_ = lean_string_push(v_out_1110_, v___x_1209_);
v_i_1109_ = v_next_1158_;
v_out_1110_ = v___x_1210_;
goto _start;
}
}
else
{
lean_object* v___x_1212_; 
lean_dec_ref(v_lit_1108_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_out_1110_);
return v___x_1212_;
}
}
}
else
{
lean_object* v___x_1213_; 
lean_dec(v_i_1109_);
lean_dec_ref(v_lit_1108_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_out_1110_);
return v___x_1213_;
}
v___jp_1114_:
{
lean_object* v_stopPos_1119_; uint32_t v_ch_1120_; lean_object* v___x_1121_; 
v_stopPos_1119_ = lean_ctor_get(v___y_1118_, 2);
lean_inc(v_stopPos_1119_);
lean_dec_ref(v___y_1118_);
v_ch_1120_ = lean_uint32_of_nat(v___y_1117_);
lean_dec(v___y_1117_);
v___x_1121_ = lean_string_push(v_out_1110_, v_ch_1120_);
v_i_1109_ = v_stopPos_1119_;
v_out_1110_ = v___x_1121_;
v_a_1111_ = v___y_1115_;
v_a_1112_ = v___y_1116_;
goto _start;
}
v___jp_1123_:
{
if (v___y_1125_ == 0)
{
if (v___y_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec(v___y_1127_);
lean_dec_ref(v_out_1110_);
lean_dec_ref(v_lit_1108_);
v___x_1130_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1);
v___x_1131_ = lean_substring_tostring(v___y_1128_);
v___x_1132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
v___x_1133_ = l_Lean_MessageData_ofFormat(v___x_1132_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1130_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v___x_1136_, v___y_1124_, v___y_1126_);
return v___x_1137_;
}
else
{
v___y_1115_ = v___y_1124_;
v___y_1116_ = v___y_1126_;
v___y_1117_ = v___y_1127_;
v___y_1118_ = v___y_1128_;
goto v___jp_1114_;
}
}
else
{
v___y_1115_ = v___y_1124_;
v___y_1116_ = v___y_1126_;
v___y_1117_ = v___y_1127_;
v___y_1118_ = v___y_1128_;
goto v___jp_1114_;
}
}
v___jp_1138_:
{
lean_object* v_val_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
lean_inc_ref(v_escape_1139_);
v_val_1142_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(v_escape_1139_);
v___x_1143_ = lean_unsigned_to_nat(55296u);
v___x_1144_ = lean_nat_dec_lt(v_val_1142_, v___x_1143_);
v___x_1145_ = lean_unsigned_to_nat(57343u);
v___x_1146_ = lean_nat_dec_lt(v___x_1145_, v_val_1142_);
if (v___x_1146_ == 0)
{
v___y_1124_ = v___y_1140_;
v___y_1125_ = v___x_1144_;
v___y_1126_ = v___y_1141_;
v___y_1127_ = v_val_1142_;
v___y_1128_ = v_escape_1139_;
v___y_1129_ = v___x_1146_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1147_; uint8_t v___x_1148_; 
v___x_1147_ = lean_unsigned_to_nat(1114112u);
v___x_1148_ = lean_nat_dec_lt(v_val_1142_, v___x_1147_);
v___y_1124_ = v___y_1140_;
v___y_1125_ = v___x_1144_;
v___y_1126_ = v___y_1141_;
v___y_1127_ = v_val_1142_;
v___y_1128_ = v_escape_1139_;
v___y_1129_ = v___x_1148_;
goto v___jp_1123_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object* v_lit_1214_, lean_object* v_i_1215_, lean_object* v_out_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v_lit_1214_, v_i_1215_, v_out_1216_, v_a_1217_, v_a_1218_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
return v_res_1220_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4));
v___x_1231_ = l_Lean_MessageData_ofFormat(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object* v_x_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_a_1237_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
v___x_1258_ = l_Lean_Syntax_isLit_x3f(v___x_1257_, v_x_1232_);
if (lean_obj_tag(v___x_1258_) == 1)
{
lean_object* v_val_1259_; 
v_val_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v_a_1237_ = v_val_1259_;
goto v___jp_1236_;
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_dec(v___x_1258_);
v___x_1260_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5);
v___x_1261_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1232_, v___x_1260_, v_a_1233_, v_a_1234_);
return v___x_1261_;
}
v___jp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_toCold_1241_; lean_object* v_currRecDepth_1242_; lean_object* v_ref_1243_; uint8_t v_diag_1244_; uint8_t v_suppressElabErrors_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_ref_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_string_utf8_byte_size(v_a_1237_);
lean_inc_ref_n(v_a_1237_, 2);
v___x_1240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1240_, 0, v_a_1237_);
lean_ctor_set(v___x_1240_, 1, v___x_1238_);
lean_ctor_set(v___x_1240_, 2, v___x_1239_);
v_toCold_1241_ = lean_ctor_get(v_a_1233_, 0);
v_currRecDepth_1242_ = lean_ctor_get(v_a_1233_, 1);
v_ref_1243_ = lean_ctor_get(v_a_1233_, 2);
v_diag_1244_ = lean_ctor_get_uint8(v_a_1233_, sizeof(void*)*3);
v_suppressElabErrors_1245_ = lean_ctor_get_uint8(v_a_1233_, sizeof(void*)*3 + 1);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = l_String_Slice_Pos_nextn(v___x_1240_, v___x_1238_, v___x_1246_);
lean_dec_ref_known(v___x_1240_, 3);
lean_inc(v___x_1247_);
v___x_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1248_, 0, v_a_1237_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
lean_ctor_set(v___x_1248_, 2, v___x_1239_);
v___x_1249_ = lean_nat_sub(v___x_1239_, v___x_1247_);
v___x_1250_ = l_String_Slice_Pos_prevn(v___x_1248_, v___x_1249_, v___x_1246_);
lean_dec_ref_known(v___x_1248_, 3);
v___x_1251_ = lean_nat_add(v___x_1247_, v___x_1250_);
lean_dec(v___x_1250_);
v___x_1252_ = lean_string_utf8_extract_fast(v_a_1237_, v___x_1247_, v___x_1251_);
lean_dec(v___x_1251_);
lean_dec(v___x_1247_);
lean_dec_ref(v_a_1237_);
v___x_1253_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1254_ = l_Lean_replaceRef(v_x_1232_, v_ref_1243_);
lean_inc(v_currRecDepth_1242_);
lean_inc_ref(v_toCold_1241_);
v___x_1255_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1255_, 0, v_toCold_1241_);
lean_ctor_set(v___x_1255_, 1, v_currRecDepth_1242_);
lean_ctor_set(v___x_1255_, 2, v_ref_1254_);
lean_ctor_set_uint8(v___x_1255_, sizeof(void*)*3, v_diag_1244_);
lean_ctor_set_uint8(v___x_1255_, sizeof(void*)*3 + 1, v_suppressElabErrors_1245_);
v___x_1256_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1252_, v___x_1238_, v___x_1253_, v___x_1255_, v_a_1234_);
lean_dec_ref_known(v___x_1255_, 3);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object* v_x_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1262_, v_a_1263_, v_a_1264_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_x_1262_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object* v_s_1267_){
_start:
{
uint32_t v___y_1269_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = lean_string_utf8_byte_size(v_s_1267_);
lean_inc_ref(v_s_1267_);
v___x_1288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1288_, 0, v_s_1267_);
lean_ctor_set(v___x_1288_, 1, v___x_1286_);
lean_ctor_set(v___x_1288_, 2, v___x_1287_);
v___x_1289_ = l_String_Slice_Pos_get_x3f(v___x_1288_, v___x_1286_);
lean_dec_ref_known(v___x_1288_, 3);
if (lean_obj_tag(v___x_1289_) == 0)
{
uint32_t v___x_1290_; 
v___x_1290_ = 65;
v___y_1269_ = v___x_1290_;
goto v___jp_1268_;
}
else
{
lean_object* v_val_1291_; uint32_t v___x_1292_; 
v_val_1291_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v___x_1289_, 1);
v___x_1292_ = lean_unbox_uint32(v_val_1291_);
lean_dec(v_val_1291_);
v___y_1269_ = v___x_1292_;
goto v___jp_1268_;
}
v___jp_1268_:
{
uint32_t v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = 13;
v___x_1271_ = lean_uint32_dec_eq(v___y_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
uint32_t v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = 10;
v___x_1273_ = lean_uint32_dec_eq(v___y_1269_, v___x_1272_);
if (v___x_1273_ == 0)
{
return v_s_1267_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1274_ = lean_unsigned_to_nat(1u);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_string_utf8_byte_size(v_s_1267_);
lean_inc_ref(v_s_1267_);
v___x_1277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1277_, 0, v_s_1267_);
lean_ctor_set(v___x_1277_, 1, v___x_1275_);
lean_ctor_set(v___x_1277_, 2, v___x_1276_);
v___x_1278_ = l_String_Slice_Pos_nextn(v___x_1277_, v___x_1275_, v___x_1274_);
lean_dec_ref_known(v___x_1277_, 3);
v___x_1279_ = lean_string_utf8_extract_fast(v_s_1267_, v___x_1278_, v___x_1276_);
lean_dec(v___x_1278_);
lean_dec_ref(v_s_1267_);
return v___x_1279_;
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1280_ = lean_unsigned_to_nat(2u);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_string_utf8_byte_size(v_s_1267_);
lean_inc_ref(v_s_1267_);
v___x_1283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1283_, 0, v_s_1267_);
lean_ctor_set(v___x_1283_, 1, v___x_1281_);
lean_ctor_set(v___x_1283_, 2, v___x_1282_);
v___x_1284_ = l_String_Slice_Pos_nextn(v___x_1283_, v___x_1281_, v___x_1280_);
lean_dec_ref_known(v___x_1283_, 3);
v___x_1285_ = lean_string_utf8_extract_fast(v_s_1267_, v___x_1284_, v___x_1282_);
lean_dec(v___x_1284_);
lean_dec_ref(v_s_1267_);
return v___x_1285_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3));
v___x_1302_ = l_Lean_MessageData_ofFormat(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object* v_x_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_a_1308_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
v___x_1322_ = l_Lean_Syntax_isLit_x3f(v___x_1321_, v_x_1303_);
if (lean_obj_tag(v___x_1322_) == 1)
{
lean_object* v_val_1323_; 
v_val_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_val_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v_a_1308_ = v_val_1323_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v___x_1322_);
v___x_1324_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4);
v___x_1325_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1303_, v___x_1324_, v_a_1304_, v_a_1305_);
return v___x_1325_;
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1309_ = lean_unsigned_to_nat(3u);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_string_utf8_byte_size(v_a_1308_);
lean_inc_ref_n(v_a_1308_, 2);
v___x_1312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1312_, 0, v_a_1308_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
lean_ctor_set(v___x_1312_, 2, v___x_1311_);
v___x_1313_ = l_String_Slice_Pos_nextn(v___x_1312_, v___x_1310_, v___x_1309_);
lean_dec_ref_known(v___x_1312_, 3);
lean_inc(v___x_1313_);
v___x_1314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1314_, 0, v_a_1308_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
lean_ctor_set(v___x_1314_, 2, v___x_1311_);
v___x_1315_ = lean_nat_sub(v___x_1311_, v___x_1313_);
v___x_1316_ = l_String_Slice_Pos_prevn(v___x_1314_, v___x_1315_, v___x_1309_);
lean_dec_ref_known(v___x_1314_, 3);
v___x_1317_ = lean_nat_add(v___x_1313_, v___x_1316_);
lean_dec(v___x_1316_);
v___x_1318_ = lean_string_utf8_extract_fast(v_a_1308_, v___x_1313_, v___x_1317_);
lean_dec(v___x_1317_);
lean_dec(v___x_1313_);
lean_dec_ref(v_a_1308_);
v___x_1319_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object* v_x_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1326_, v_a_1327_, v_a_1328_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_x_1326_);
return v_res_1330_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3));
v___x_1340_ = l_Lean_MessageData_ofFormat(v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object* v_x_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_a_1346_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
v___x_1368_ = l_Lean_Syntax_isLit_x3f(v___x_1367_, v_x_1341_);
if (lean_obj_tag(v___x_1368_) == 1)
{
lean_object* v_val_1369_; 
v_val_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v_a_1346_ = v_val_1369_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec(v___x_1368_);
v___x_1370_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4);
v___x_1371_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1341_, v___x_1370_, v_a_1342_, v_a_1343_);
return v___x_1371_;
}
v___jp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_toCold_1350_; lean_object* v_currRecDepth_1351_; lean_object* v_ref_1352_; uint8_t v_diag_1353_; uint8_t v_suppressElabErrors_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v_ref_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_string_utf8_byte_size(v_a_1346_);
lean_inc_ref_n(v_a_1346_, 2);
v___x_1349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1349_, 0, v_a_1346_);
lean_ctor_set(v___x_1349_, 1, v___x_1347_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
v_toCold_1350_ = lean_ctor_get(v_a_1342_, 0);
v_currRecDepth_1351_ = lean_ctor_get(v_a_1342_, 1);
v_ref_1352_ = lean_ctor_get(v_a_1342_, 2);
v_diag_1353_ = lean_ctor_get_uint8(v_a_1342_, sizeof(void*)*3);
v_suppressElabErrors_1354_ = lean_ctor_get_uint8(v_a_1342_, sizeof(void*)*3 + 1);
v___x_1355_ = lean_unsigned_to_nat(3u);
v___x_1356_ = l_String_Slice_Pos_nextn(v___x_1349_, v___x_1347_, v___x_1355_);
lean_dec_ref_known(v___x_1349_, 3);
lean_inc(v___x_1356_);
v___x_1357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1357_, 0, v_a_1346_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
lean_ctor_set(v___x_1357_, 2, v___x_1348_);
v___x_1358_ = lean_nat_sub(v___x_1348_, v___x_1356_);
v___x_1359_ = l_String_Slice_Pos_prevn(v___x_1357_, v___x_1358_, v___x_1355_);
lean_dec_ref_known(v___x_1357_, 3);
v___x_1360_ = lean_nat_add(v___x_1356_, v___x_1359_);
lean_dec(v___x_1359_);
v___x_1361_ = lean_string_utf8_extract_fast(v_a_1346_, v___x_1356_, v___x_1360_);
lean_dec(v___x_1360_);
lean_dec(v___x_1356_);
lean_dec_ref(v_a_1346_);
v___x_1362_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1361_);
v___x_1363_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1364_ = l_Lean_replaceRef(v_x_1341_, v_ref_1352_);
lean_inc(v_currRecDepth_1351_);
lean_inc_ref(v_toCold_1350_);
v___x_1365_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1365_, 0, v_toCold_1350_);
lean_ctor_set(v___x_1365_, 1, v_currRecDepth_1351_);
lean_ctor_set(v___x_1365_, 2, v_ref_1364_);
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*3, v_diag_1353_);
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*3 + 1, v_suppressElabErrors_1354_);
v___x_1366_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1362_, v___x_1347_, v___x_1363_, v___x_1365_, v_a_1343_);
lean_dec_ref_known(v___x_1365_, 3);
return v___x_1366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object* v_x_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_x_1372_);
return v_res_1376_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2));
v___x_1384_ = l_Lean_stringToMessageData(v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object* v_x_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_1385_);
v___x_1390_ = l_Lean_Syntax_isOfKind(v_x_1385_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1392_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1385_, v___x_1391_, v_a_1386_, v_a_1387_);
lean_dec(v_x_1385_);
return v___x_1392_;
}
else
{
lean_object* v___x_1393_; lean_object* v_x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v_x_1394_ = l_Lean_Syntax_getArg(v_x_1385_, v___x_1393_);
v___x_1395_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1394_);
v___x_1396_ = l_Lean_Syntax_isOfKind(v_x_1394_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1394_);
v___x_1398_ = l_Lean_Syntax_isOfKind(v_x_1394_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
lean_inc(v_x_1394_);
v___x_1400_ = l_Lean_Syntax_isOfKind(v_x_1394_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
lean_inc(v_x_1394_);
v___x_1402_ = l_Lean_Syntax_isOfKind(v_x_1394_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_x_1394_);
v___x_1403_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1404_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1385_, v___x_1403_, v_a_1386_, v_a_1387_);
lean_dec(v_x_1385_);
return v___x_1404_;
}
else
{
lean_object* v___x_1405_; 
lean_dec(v_x_1385_);
v___x_1405_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1394_, v_a_1386_, v_a_1387_);
lean_dec(v_x_1394_);
return v___x_1405_;
}
}
else
{
lean_object* v___x_1406_; 
lean_dec(v_x_1385_);
v___x_1406_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1394_, v_a_1386_, v_a_1387_);
lean_dec(v_x_1394_);
return v___x_1406_;
}
}
else
{
lean_object* v___x_1407_; 
lean_dec(v_x_1385_);
v___x_1407_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1394_, v_a_1386_, v_a_1387_);
lean_dec(v_x_1394_);
return v___x_1407_;
}
}
else
{
lean_object* v___x_1408_; 
lean_dec(v_x_1385_);
v___x_1408_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1394_, v_a_1386_, v_a_1387_);
lean_dec(v_x_1394_);
return v___x_1408_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object* v_x_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
return v_res_1413_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3));
v___x_1423_ = l_Lean_MessageData_ofFormat(v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object* v_x_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v___x_1428_; lean_object* v_toApplicative_1429_; lean_object* v_toFunctor_1430_; lean_object* v_toSeq_1431_; lean_object* v_toSeqLeft_1432_; lean_object* v_toSeqRight_1433_; lean_object* v___x_1434_; lean_object* v___f_1435_; lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1428_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_1429_ = lean_ctor_get(v___x_1428_, 0);
v_toFunctor_1430_ = lean_ctor_get(v_toApplicative_1429_, 0);
v_toSeq_1431_ = lean_ctor_get(v_toApplicative_1429_, 2);
v_toSeqLeft_1432_ = lean_ctor_get(v_toApplicative_1429_, 3);
v_toSeqRight_1433_ = lean_ctor_get(v_toApplicative_1429_, 4);
v___x_1434_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
v___f_1435_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_1436_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref_n(v_toFunctor_1430_, 2);
v___f_1437_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1437_, 0, v_toFunctor_1430_);
v___f_1438_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1438_, 0, v_toFunctor_1430_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___f_1437_);
lean_ctor_set(v___x_1439_, 1, v___f_1438_);
lean_inc(v_toSeqRight_1433_);
v___f_1440_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1440_, 0, v_toSeqRight_1433_);
lean_inc(v_toSeqLeft_1432_);
v___f_1441_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1441_, 0, v_toSeqLeft_1432_);
lean_inc(v_toSeq_1431_);
v___f_1442_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1442_, 0, v_toSeq_1431_);
v___x_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1439_);
lean_ctor_set(v___x_1443_, 1, v___f_1435_);
lean_ctor_set(v___x_1443_, 2, v___f_1442_);
lean_ctor_set(v___x_1443_, 3, v___f_1441_);
lean_ctor_set(v___x_1443_, 4, v___f_1440_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v___f_1436_);
v___x_1445_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_1446_ = l_Lean_Core_instMonadRefCoreM;
v___x_1447_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_1444_);
v___x_1448_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1447_, v___x_1444_);
v___x_1449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1445_);
lean_ctor_set(v___x_1449_, 1, v___x_1446_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
v___x_1450_ = l_Lean_Syntax_isLit_x3f(v___x_1434_, v_x_1424_);
if (lean_obj_tag(v___x_1450_) == 1)
{
lean_object* v_val_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref_known(v___x_1449_, 3);
lean_dec_ref_known(v___x_1444_, 2);
lean_dec(v_x_1424_);
v_val_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_val_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set_tag(v___x_1453_, 0);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_val_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
else
{
lean_object* v___x_1459_; lean_object* v___x_25__overap_1460_; lean_object* v___x_1461_; 
lean_dec(v___x_1450_);
v___x_1459_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_25__overap_1460_ = l_Lean_throwErrorAt___redArg(v___x_1444_, v___x_1449_, v_x_1424_, v___x_1459_);
lean_inc(v_a_1426_);
lean_inc_ref(v_a_1425_);
v___x_1461_ = lean_apply_3(v___x_25__overap_1460_, v_a_1425_, v_a_1426_, lean_box(0));
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object* v_x_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(v_x_1462_, v_a_1463_, v_a_1464_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1466_;
}
}
static lean_object* _init_l_Lake_Toml_elabSimpleKey___closed__3(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__2));
v___x_1474_ = l_Lean_stringToMessageData(v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object* v_x_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__1));
lean_inc(v_x_1475_);
v___x_1480_ = l_Lean_Syntax_isOfKind(v_x_1475_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1482_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1475_, v___x_1481_, v_a_1476_, v_a_1477_);
lean_dec(v_x_1475_);
return v___x_1482_;
}
else
{
lean_object* v___x_1483_; lean_object* v_x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1483_ = lean_unsigned_to_nat(0u);
v_x_1484_ = l_Lean_Syntax_getArg(v_x_1475_, v___x_1483_);
v___x_1485_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
lean_inc(v_x_1484_);
v___x_1486_ = l_Lean_Syntax_isOfKind(v_x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1484_);
v___x_1488_ = l_Lean_Syntax_isOfKind(v_x_1484_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; uint8_t v___x_1490_; 
v___x_1489_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1484_);
v___x_1490_ = l_Lean_Syntax_isOfKind(v_x_1484_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_dec(v_x_1484_);
v___x_1491_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1492_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1475_, v___x_1491_, v_a_1476_, v_a_1477_);
lean_dec(v_x_1475_);
return v___x_1492_;
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_x_1475_);
v___x_1493_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1484_, v_a_1476_, v_a_1477_);
lean_dec(v_x_1484_);
return v___x_1493_;
}
}
else
{
lean_object* v___x_1494_; 
lean_dec(v_x_1475_);
v___x_1494_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1484_, v_a_1476_, v_a_1477_);
lean_dec(v_x_1484_);
return v___x_1494_;
}
}
else
{
lean_object* v___x_1495_; 
lean_dec(v_x_1475_);
v___x_1495_ = l_Lean_Syntax_isLit_x3f(v___x_1485_, v_x_1484_);
if (lean_obj_tag(v___x_1495_) == 1)
{
lean_object* v_val_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec(v_x_1484_);
v_val_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_val_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 0);
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_val_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec(v___x_1495_);
v___x_1504_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_1505_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1484_, v___x_1504_, v_a_1476_, v_a_1477_);
lean_dec(v_x_1484_);
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object* v_x_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lake_Toml_elabSimpleKey(v_x_1506_, v_a_1507_, v_a_1508_);
lean_dec(v_a_1508_);
lean_dec_ref(v_a_1507_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object* v_elabVal_1511_, size_t v_sz_1512_, size_t v_i_1513_, lean_object* v_bs_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
uint8_t v___x_1518_; 
v___x_1518_ = lean_usize_dec_lt(v_i_1513_, v_sz_1512_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; 
lean_dec_ref(v_elabVal_1511_);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v_bs_1514_);
return v___x_1519_;
}
else
{
lean_object* v_v_1520_; lean_object* v___x_1521_; 
v_v_1520_ = lean_array_uget_borrowed(v_bs_1514_, v_i_1513_);
lean_inc_ref(v_elabVal_1511_);
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
lean_inc(v_v_1520_);
v___x_1521_ = lean_apply_4(v_elabVal_1511_, v_v_1520_, v___y_1515_, v___y_1516_, lean_box(0));
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; lean_object* v_bs_x27_1524_; size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = lean_unsigned_to_nat(0u);
v_bs_x27_1524_ = lean_array_uset(v_bs_1514_, v_i_1513_, v___x_1523_);
v___x_1525_ = ((size_t)1ULL);
v___x_1526_ = lean_usize_add(v_i_1513_, v___x_1525_);
v___x_1527_ = lean_array_uset(v_bs_x27_1524_, v_i_1513_, v_a_1522_);
v_i_1513_ = v___x_1526_;
v_bs_1514_ = v___x_1527_;
goto _start;
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec_ref(v_bs_1514_);
lean_dec_ref(v_elabVal_1511_);
v_a_1529_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1521_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1521_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object* v_elabVal_1537_, lean_object* v_sz_1538_, lean_object* v_i_1539_, lean_object* v_bs_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
size_t v_sz_boxed_1544_; size_t v_i_boxed_1545_; lean_object* v_res_1546_; 
v_sz_boxed_1544_ = lean_unbox_usize(v_sz_1538_);
lean_dec(v_sz_1538_);
v_i_boxed_1545_ = lean_unbox_usize(v_i_1539_);
lean_dec(v_i_1539_);
v_res_1546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1537_, v_sz_boxed_1544_, v_i_boxed_1545_, v_bs_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1546_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object* v_x_1555_, lean_object* v_elabVal_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_1555_);
v___x_1561_ = l_Lean_Syntax_isOfKind(v_x_1555_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec_ref(v_elabVal_1556_);
v___x_1562_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3);
v___x_1563_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1555_, v___x_1562_, v_a_1557_, v_a_1558_);
lean_dec(v_x_1555_);
return v___x_1563_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v_xs_1566_; lean_object* v___x_1567_; size_t v_sz_1568_; size_t v___x_1569_; lean_object* v___x_1570_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
v___x_1565_ = l_Lean_Syntax_getArg(v_x_1555_, v___x_1564_);
lean_dec(v_x_1555_);
v_xs_1566_ = l_Lean_Syntax_getArgs(v___x_1565_);
lean_dec(v___x_1565_);
v___x_1567_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1566_);
lean_dec_ref(v_xs_1566_);
v_sz_1568_ = lean_array_size(v___x_1567_);
v___x_1569_ = ((size_t)0ULL);
v___x_1570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1556_, v_sz_1568_, v___x_1569_, v___x_1567_, v_a_1557_, v_a_1558_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object* v_x_1571_, lean_object* v_elabVal_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1571_, v_elabVal_1572_, v_a_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object* v_00_u03b1_1577_, lean_object* v_x_1578_, lean_object* v_elabVal_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1578_, v_elabVal_1579_, v_a_1580_, v_a_1581_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object* v_00_u03b1_1584_, lean_object* v_x_1585_, lean_object* v_elabVal_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(v_00_u03b1_1584_, v_x_1585_, v_elabVal_1586_, v_a_1587_, v_a_1588_);
lean_dec(v_a_1588_);
lean_dec_ref(v_a_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object* v_00_u03b1_1591_, lean_object* v_elabVal_1592_, size_t v_sz_1593_, size_t v_i_1594_, lean_object* v_bs_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1592_, v_sz_1593_, v_i_1594_, v_bs_1595_, v___y_1596_, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object* v_00_u03b1_1600_, lean_object* v_elabVal_1601_, lean_object* v_sz_1602_, lean_object* v_i_1603_, lean_object* v_bs_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1602_);
lean_dec(v_sz_1602_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1603_);
lean_dec(v_i_1603_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(v_00_u03b1_1600_, v_elabVal_1601_, v_sz_boxed_1608_, v_i_boxed_1609_, v_bs_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(size_t v_sz_1611_, size_t v_i_1612_, lean_object* v_bs_1613_){
_start:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_usize_dec_lt(v_i_1612_, v_sz_1611_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1615_, 0, v_bs_1613_);
return v___x_1615_;
}
else
{
lean_object* v_v_1616_; lean_object* v___x_1617_; lean_object* v_bs_x27_1618_; size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
v_v_1616_ = lean_array_uget(v_bs_1613_, v_i_1612_);
v___x_1617_ = lean_unsigned_to_nat(0u);
v_bs_x27_1618_ = lean_array_uset(v_bs_1613_, v_i_1612_, v___x_1617_);
v___x_1619_ = ((size_t)1ULL);
v___x_1620_ = lean_usize_add(v_i_1612_, v___x_1619_);
v___x_1621_ = lean_array_uset(v_bs_x27_1618_, v_i_1612_, v_v_1616_);
v_i_1612_ = v___x_1620_;
v_bs_1613_ = v___x_1621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object* v_sz_1623_, lean_object* v_i_1624_, lean_object* v_bs_1625_){
_start:
{
size_t v_sz_boxed_1626_; size_t v_i_boxed_1627_; lean_object* v_res_1628_; 
v_sz_boxed_1626_ = lean_unbox_usize(v_sz_1623_);
lean_dec(v_sz_1623_);
v_i_boxed_1627_ = lean_unbox_usize(v_i_1624_);
lean_dec(v_i_1624_);
v_res_1628_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_sz_boxed_1626_, v_i_boxed_1627_, v_bs_1625_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(lean_object* v_msg_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_ref_1633_; lean_object* v___x_1634_; lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1643_; 
v_ref_1633_ = lean_ctor_get(v___y_1630_, 2);
v___x_1634_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_1629_, v___y_1630_, v___y_1631_);
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1643_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_inc(v_ref_1633_);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v_ref_1633_);
lean_ctor_set(v___x_1639_, 1, v_a_1635_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set_tag(v___x_1637_, 1);
lean_ctor_set(v___x_1637_, 0, v___x_1639_);
v___x_1641_ = v___x_1637_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(lean_object* v_ref_1649_, lean_object* v_msg_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_toCold_1655_; lean_object* v_currRecDepth_1656_; lean_object* v_ref_1657_; uint8_t v_diag_1658_; uint8_t v_suppressElabErrors_1659_; lean_object* v_ref_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_toCold_1655_ = lean_ctor_get(v___y_1652_, 0);
v_currRecDepth_1656_ = lean_ctor_get(v___y_1652_, 1);
v_ref_1657_ = lean_ctor_get(v___y_1652_, 2);
v_diag_1658_ = lean_ctor_get_uint8(v___y_1652_, sizeof(void*)*3);
v_suppressElabErrors_1659_ = lean_ctor_get_uint8(v___y_1652_, sizeof(void*)*3 + 1);
v_ref_1660_ = l_Lean_replaceRef(v_ref_1649_, v_ref_1657_);
lean_inc(v_currRecDepth_1656_);
lean_inc_ref(v_toCold_1655_);
v___x_1661_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1661_, 0, v_toCold_1655_);
lean_ctor_set(v___x_1661_, 1, v_currRecDepth_1656_);
lean_ctor_set(v___x_1661_, 2, v_ref_1660_);
lean_ctor_set_uint8(v___x_1661_, sizeof(void*)*3, v_diag_1658_);
lean_ctor_set_uint8(v___x_1661_, sizeof(void*)*3 + 1, v_suppressElabErrors_1659_);
v___x_1662_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_1650_, v___x_1661_, v___y_1653_);
lean_dec_ref_known(v___x_1661_, 3);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg___boxed(lean_object* v_ref_1663_, lean_object* v_msg_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v_ref_1663_, v_msg_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v_ref_1663_);
return v_res_1669_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1));
v___x_1673_ = l_Lean_stringToMessageData(v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object* v_t_1674_, uint8_t v___x_1675_, lean_object* v_as_1676_, size_t v_i_1677_, size_t v_stop_1678_, lean_object* v_b_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_fst_1685_; lean_object* v_snd_1686_; uint8_t v___x_1690_; 
v___x_1690_ = lean_usize_dec_eq(v_i_1677_, v_stop_1678_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_array_uget_borrowed(v_as_1676_, v_i_1677_);
lean_inc(v___x_1691_);
v___x_1692_ = l_Lake_Toml_elabSimpleKey(v___x_1691_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1713_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1695_ = l_Lean_Name_str___override(v_b_1679_, v_a_1693_);
lean_inc_ref(v_t_1674_);
lean_inc(v___x_1695_);
v___x_1713_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1694_, v___x_1695_, v_t_1674_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = lean_box(0);
lean_inc(v___x_1695_);
v___x_1715_ = l_Lake_Toml_RBDict_push___redArg(v___x_1694_, v___x_1695_, v___x_1714_, v___y_1680_);
v_fst_1685_ = v___x_1695_;
v_snd_1686_ = v___x_1715_;
goto v___jp_1684_;
}
else
{
lean_object* v_val_1716_; lean_object* v_snd_1717_; 
v_val_1716_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_val_1716_);
lean_dec_ref_known(v___x_1713_, 1);
v_snd_1717_ = lean_ctor_get(v_val_1716_, 1);
lean_inc(v_snd_1717_);
lean_dec(v_val_1716_);
if (lean_obj_tag(v_snd_1717_) == 0)
{
if (v___x_1675_ == 0)
{
goto v___jp_1696_;
}
else
{
v_fst_1685_ = v___x_1695_;
v_snd_1686_ = v___y_1680_;
goto v___jp_1684_;
}
}
else
{
lean_dec_ref_known(v_snd_1717_, 1);
goto v___jp_1696_;
}
}
v___jp_1696_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1697_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
lean_inc(v___x_1695_);
v___x_1698_ = l_Lean_MessageData_ofName(v___x_1695_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v___x_1691_, v___x_1701_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec_ref(v___y_1680_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v_snd_1704_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v_snd_1704_ = lean_ctor_get(v_a_1703_, 1);
lean_inc(v_snd_1704_);
lean_dec(v_a_1703_);
v_fst_1685_ = v___x_1695_;
v_snd_1686_ = v_snd_1704_;
goto v___jp_1684_;
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v___x_1695_);
lean_dec_ref(v_t_1674_);
v_a_1705_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1702_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1702_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v___y_1680_);
lean_dec(v_b_1679_);
lean_dec_ref(v_t_1674_);
v_a_1718_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1692_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1692_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v_t_1674_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_b_1679_);
lean_ctor_set(v___x_1726_, 1, v___y_1680_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
v___jp_1684_:
{
size_t v___x_1687_; size_t v___x_1688_; 
v___x_1687_ = ((size_t)1ULL);
v___x_1688_ = lean_usize_add(v_i_1677_, v___x_1687_);
v_i_1677_ = v___x_1688_;
v_b_1679_ = v_fst_1685_;
v___y_1680_ = v_snd_1686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object* v_t_1728_, lean_object* v___x_1729_, lean_object* v_as_1730_, lean_object* v_i_1731_, lean_object* v_stop_1732_, lean_object* v_b_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
uint8_t v___x_7009__boxed_1738_; size_t v_i_boxed_1739_; size_t v_stop_boxed_1740_; lean_object* v_res_1741_; 
v___x_7009__boxed_1738_ = lean_unbox(v___x_1729_);
v_i_boxed_1739_ = lean_unbox_usize(v_i_1731_);
lean_dec(v_i_1731_);
v_stop_boxed_1740_ = lean_unbox_usize(v_stop_1732_);
lean_dec(v_stop_1732_);
v_res_1741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_t_1728_, v___x_7009__boxed_1738_, v_as_1730_, v_i_boxed_1739_, v_stop_boxed_1740_, v_b_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v_as_1730_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t v___x_1742_, lean_object* v_as_1743_, size_t v_i_1744_, size_t v_stop_1745_, lean_object* v_b_1746_){
_start:
{
lean_object* v___y_1748_; uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_eq(v_i_1744_, v_stop_1745_);
if (v___x_1752_ == 0)
{
lean_object* v_fst_1753_; uint8_t v___x_1754_; 
v_fst_1753_ = lean_ctor_get(v_b_1746_, 0);
v___x_1754_ = lean_unbox(v_fst_1753_);
if (v___x_1754_ == 0)
{
lean_object* v_snd_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1763_; 
v_snd_1755_ = lean_ctor_get(v_b_1746_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_b_1746_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v_b_1746_, 0);
lean_dec(v_unused_1764_);
v___x_1757_ = v_b_1746_;
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_snd_1755_);
lean_dec(v_b_1746_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_box(v___x_1742_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1759_);
v___x_1761_ = v___x_1757_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_snd_1755_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
v___y_1748_ = v___x_1761_;
goto v___jp_1747_;
}
}
}
else
{
lean_object* v_snd_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1775_; 
v_snd_1765_ = lean_ctor_get(v_b_1746_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_b_1746_);
if (v_isSharedCheck_1775_ == 0)
{
lean_object* v_unused_1776_; 
v_unused_1776_ = lean_ctor_get(v_b_1746_, 0);
lean_dec(v_unused_1776_);
v___x_1767_ = v_b_1746_;
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_snd_1765_);
lean_dec(v_b_1746_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1775_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1769_ = lean_array_uget_borrowed(v_as_1743_, v_i_1744_);
lean_inc(v___x_1769_);
v___x_1770_ = lean_array_push(v_snd_1765_, v___x_1769_);
v___x_1771_ = lean_box(v___x_1752_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___x_1770_);
lean_ctor_set(v___x_1767_, 0, v___x_1771_);
v___x_1773_ = v___x_1767_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1770_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
v___y_1748_ = v___x_1773_;
goto v___jp_1747_;
}
}
}
}
else
{
return v_b_1746_;
}
v___jp_1747_:
{
size_t v___x_1749_; size_t v___x_1750_; 
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_add(v_i_1744_, v___x_1749_);
v_i_1744_ = v___x_1750_;
v_b_1746_ = v___y_1748_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object* v___x_1777_, lean_object* v_as_1778_, lean_object* v_i_1779_, lean_object* v_stop_1780_, lean_object* v_b_1781_){
_start:
{
uint8_t v___x_7116__boxed_1782_; size_t v_i_boxed_1783_; size_t v_stop_boxed_1784_; lean_object* v_res_1785_; 
v___x_7116__boxed_1782_ = lean_unbox(v___x_1777_);
v_i_boxed_1783_ = lean_unbox_usize(v_i_1779_);
lean_dec(v_i_1779_);
v_stop_boxed_1784_ = lean_unbox_usize(v_stop_1780_);
lean_dec(v_stop_1780_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_7116__boxed_1782_, v_as_1778_, v_i_boxed_1783_, v_stop_boxed_1784_, v_b_1781_);
lean_dec_ref(v_as_1778_);
return v_res_1785_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2));
v___x_1793_ = l_Lean_stringToMessageData(v___x_1792_);
return v___x_1793_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6));
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object* v_elabVal_1804_, lean_object* v_as_1805_, size_t v_i_1806_, size_t v_stop_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_a_1813_; lean_object* v___y_1818_; uint8_t v___x_1820_; 
v___x_1820_ = lean_usize_dec_eq(v_i_1806_, v_stop_1807_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v___x_1821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1));
v___x_1822_ = lean_array_uget_borrowed(v_as_1805_, v_i_1806_);
lean_inc(v___x_1822_);
v___x_1823_ = l_Lean_Syntax_isOfKind(v___x_1822_, v___x_1821_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec_ref(v_b_1808_);
v___x_1824_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3);
v___x_1825_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1822_, v___x_1824_, v___y_1809_, v___y_1810_);
v___y_1818_ = v___x_1825_;
goto v___jp_1817_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1826_ = lean_unsigned_to_nat(0u);
v___x_1827_ = l_Lean_Syntax_getArg(v___x_1822_, v___x_1826_);
v___x_1828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5));
lean_inc(v___x_1827_);
v___x_1829_ = l_Lean_Syntax_isOfKind(v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_b_1808_);
v___x_1830_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1831_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1827_, v___x_1830_, v___y_1809_, v___y_1810_);
lean_dec(v___x_1827_);
v___y_1818_ = v___x_1831_;
goto v___jp_1817_;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_v_1834_; lean_object* v___y_1836_; lean_object* v_fst_1837_; lean_object* v_snd_1838_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1884_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1833_ = lean_unsigned_to_nat(2u);
v_v_1834_ = l_Lean_Syntax_getArg(v___x_1822_, v___x_1833_);
v___x_1905_ = l_Lean_Syntax_getArg(v___x_1827_, v___x_1826_);
v___x_1906_ = l_Lean_Syntax_getArgs(v___x_1905_);
lean_dec(v___x_1905_);
v___x_1907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8));
v___x_1908_ = lean_array_get_size(v___x_1906_);
v___x_1909_ = lean_nat_dec_lt(v___x_1826_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_dec_ref(v___x_1906_);
v___y_1884_ = v___x_1907_;
goto v___jp_1883_;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; size_t v___x_1912_; size_t v___x_1913_; lean_object* v___x_1914_; lean_object* v_snd_1915_; 
v___x_1910_ = lean_box(v___x_1909_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1907_);
v___x_1912_ = ((size_t)0ULL);
v___x_1913_ = lean_usize_of_nat(v___x_1908_);
v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1829_, v___x_1906_, v___x_1912_, v___x_1913_, v___x_1911_);
lean_dec_ref(v___x_1906_);
v_snd_1915_ = lean_ctor_get(v___x_1914_, 1);
lean_inc(v_snd_1915_);
lean_dec_ref(v___x_1914_);
v___y_1884_ = v_snd_1915_;
goto v___jp_1883_;
}
v___jp_1835_:
{
lean_object* v___x_1839_; 
lean_inc(v___y_1836_);
v___x_1839_ = l_Lake_Toml_elabSimpleKey(v___y_1836_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v___x_1841_ = l_Lean_Name_str___override(v_fst_1837_, v_a_1840_);
lean_inc_ref(v_snd_1838_);
lean_inc(v___x_1841_);
v___x_1842_ = l_Lake_Toml_RBDict_contains___redArg(v___x_1832_, v___x_1841_, v_snd_1838_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_dec(v___y_1836_);
lean_inc_ref(v_elabVal_1804_);
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
v___x_1843_ = lean_apply_4(v_elabVal_1804_, v_v_1834_, v___y_1809_, v___y_1810_, lean_box(0));
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref_known(v___x_1843_, 1);
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_a_1844_);
v___x_1846_ = l_Lake_Toml_RBDict_push___redArg(v___x_1832_, v___x_1841_, v___x_1845_, v_snd_1838_);
v_a_1813_ = v___x_1846_;
goto v___jp_1812_;
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v___x_1841_);
lean_dec_ref(v_snd_1838_);
lean_dec_ref(v_elabVal_1804_);
v_a_1847_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1843_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1843_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
lean_dec_ref(v_snd_1838_);
lean_dec(v_v_1834_);
v___x_1855_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
v___x_1856_ = l_Lean_MessageData_ofName(v___x_1841_);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___y_1836_, v___x_1859_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1836_);
v___y_1818_ = v___x_1860_;
goto v___jp_1817_;
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_snd_1838_);
lean_dec(v_fst_1837_);
lean_dec(v___y_1836_);
lean_dec(v_v_1834_);
lean_dec_ref(v_elabVal_1804_);
v_a_1861_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1839_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1839_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
v___jp_1869_:
{
if (lean_obj_tag(v___y_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v_fst_1873_; lean_object* v_snd_1874_; 
v_a_1872_ = lean_ctor_get(v___y_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___y_1871_, 1);
v_fst_1873_ = lean_ctor_get(v_a_1872_, 0);
lean_inc(v_fst_1873_);
v_snd_1874_ = lean_ctor_get(v_a_1872_, 1);
lean_inc(v_snd_1874_);
lean_dec(v_a_1872_);
v___y_1836_ = v___y_1870_;
v_fst_1837_ = v_fst_1873_;
v_snd_1838_ = v_snd_1874_;
goto v___jp_1835_;
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
lean_dec(v___y_1870_);
lean_dec(v_v_1834_);
lean_dec_ref(v_elabVal_1804_);
v_a_1875_ = lean_ctor_get(v___y_1871_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___y_1871_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___y_1871_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___y_1871_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
v___jp_1883_:
{
size_t v_sz_1885_; size_t v___x_1886_; lean_object* v___x_1887_; 
v_sz_1885_ = lean_array_size(v___y_1884_);
v___x_1886_ = ((size_t)0ULL);
v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_sz_1885_, v___x_1886_, v___y_1884_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec(v_v_1834_);
lean_dec_ref(v_b_1808_);
v___x_1888_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1889_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1827_, v___x_1888_, v___y_1809_, v___y_1810_);
lean_dec(v___x_1827_);
v___y_1818_ = v___x_1889_;
goto v___jp_1817_;
}
else
{
lean_object* v_val_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v_tailKey_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
lean_dec(v___x_1827_);
v_val_1890_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_val_1890_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_array_get_size(v_val_1890_);
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = lean_nat_sub(v___x_1892_, v___x_1893_);
v_tailKey_1895_ = lean_array_get(v___x_1891_, v_val_1890_, v___x_1894_);
lean_dec(v___x_1894_);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_array_pop(v_val_1890_);
v___x_1898_ = lean_array_get_size(v___x_1897_);
v___x_1899_ = lean_nat_dec_lt(v___x_1826_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_dec_ref(v___x_1897_);
v___y_1836_ = v_tailKey_1895_;
v_fst_1837_ = v___x_1896_;
v_snd_1838_ = v_b_1808_;
goto v___jp_1835_;
}
else
{
uint8_t v___x_1900_; 
v___x_1900_ = lean_nat_dec_le(v___x_1898_, v___x_1898_);
if (v___x_1900_ == 0)
{
if (v___x_1899_ == 0)
{
lean_dec_ref(v___x_1897_);
v___y_1836_ = v_tailKey_1895_;
v_fst_1837_ = v___x_1896_;
v_snd_1838_ = v_b_1808_;
goto v___jp_1835_;
}
else
{
size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_usize_of_nat(v___x_1898_);
lean_inc_ref(v_b_1808_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1808_, v___x_1829_, v___x_1897_, v___x_1886_, v___x_1901_, v___x_1896_, v_b_1808_, v___y_1809_, v___y_1810_);
lean_dec_ref(v___x_1897_);
v___y_1870_ = v_tailKey_1895_;
v___y_1871_ = v___x_1902_;
goto v___jp_1869_;
}
}
else
{
size_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_usize_of_nat(v___x_1898_);
lean_inc_ref(v_b_1808_);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1808_, v___x_1829_, v___x_1897_, v___x_1886_, v___x_1903_, v___x_1896_, v_b_1808_, v___y_1809_, v___y_1810_);
lean_dec_ref(v___x_1897_);
v___y_1870_ = v_tailKey_1895_;
v___y_1871_ = v___x_1904_;
goto v___jp_1869_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1916_; 
lean_dec_ref(v_elabVal_1804_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_b_1808_);
return v___x_1916_;
}
v___jp_1812_:
{
size_t v___x_1814_; size_t v___x_1815_; 
v___x_1814_ = ((size_t)1ULL);
v___x_1815_ = lean_usize_add(v_i_1806_, v___x_1814_);
v_i_1806_ = v___x_1815_;
v_b_1808_ = v_a_1813_;
goto _start;
}
v___jp_1817_:
{
if (lean_obj_tag(v___y_1818_) == 0)
{
lean_object* v_a_1819_; 
v_a_1819_ = lean_ctor_get(v___y_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___y_1818_, 1);
v_a_1813_ = v_a_1819_;
goto v___jp_1812_;
}
else
{
lean_dec_ref(v_elabVal_1804_);
return v___y_1818_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object* v_elabVal_1917_, lean_object* v_as_1918_, lean_object* v_i_1919_, lean_object* v_stop_1920_, lean_object* v_b_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
size_t v_i_boxed_1925_; size_t v_stop_boxed_1926_; lean_object* v_res_1927_; 
v_i_boxed_1925_ = lean_unbox_usize(v_i_1919_);
lean_dec(v_i_1919_);
v_stop_boxed_1926_ = lean_unbox_usize(v_stop_1920_);
lean_dec(v_stop_1920_);
v_res_1927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1917_, v_as_1918_, v_i_boxed_1925_, v_stop_boxed_1926_, v_b_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec_ref(v_as_1918_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object* v_as_1928_, size_t v_i_1929_, size_t v_stop_1930_, lean_object* v_b_1931_){
_start:
{
lean_object* v___y_1933_; uint8_t v___x_1937_; 
v___x_1937_ = lean_usize_dec_eq(v_i_1929_, v_stop_1930_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v_snd_1939_; 
v___x_1938_ = lean_array_uget_borrowed(v_as_1928_, v_i_1929_);
v_snd_1939_ = lean_ctor_get(v___x_1938_, 1);
if (lean_obj_tag(v_snd_1939_) == 1)
{
lean_object* v_fst_1940_; lean_object* v_val_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_fst_1940_ = lean_ctor_get(v___x_1938_, 0);
v_val_1941_ = lean_ctor_get(v_snd_1939_, 0);
v___x_1942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
lean_inc(v_val_1941_);
lean_inc(v_fst_1940_);
v___x_1943_ = l_Lake_Toml_RBDict_push___redArg(v___x_1942_, v_fst_1940_, v_val_1941_, v_b_1931_);
v___y_1933_ = v___x_1943_;
goto v___jp_1932_;
}
else
{
v___y_1933_ = v_b_1931_;
goto v___jp_1932_;
}
}
else
{
return v_b_1931_;
}
v___jp_1932_:
{
size_t v___x_1934_; size_t v___x_1935_; 
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_add(v_i_1929_, v___x_1934_);
v_i_1929_ = v___x_1935_;
v_b_1931_ = v___y_1933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object* v_as_1944_, lean_object* v_i_1945_, lean_object* v_stop_1946_, lean_object* v_b_1947_){
_start:
{
size_t v_i_boxed_1948_; size_t v_stop_boxed_1949_; lean_object* v_res_1950_; 
v_i_boxed_1948_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_stop_boxed_1949_ = lean_unbox_usize(v_stop_1946_);
lean_dec(v_stop_1946_);
v_res_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_as_1944_, v_i_boxed_1948_, v_stop_boxed_1949_, v_b_1947_);
lean_dec_ref(v_as_1944_);
return v_res_1950_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2));
v___x_1958_ = l_Lean_stringToMessageData(v___x_1957_);
return v___x_1958_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1960_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5(void){
_start:
{
lean_object* v___x_1961_; lean_object* v_t_1962_; 
v___x_1961_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v_t_1962_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_1961_);
return v_t_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object* v_x_1963_, lean_object* v_elabVal_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_1963_);
v___x_1969_ = l_Lean_Syntax_isOfKind(v_x_1963_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref(v_elabVal_1964_);
v___x_1970_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3);
v___x_1971_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1963_, v___x_1970_, v_a_1965_, v_a_1966_);
lean_dec(v_x_1963_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v_kvs_1975_; lean_object* v_a_1977_; lean_object* v___y_1988_; lean_object* v_t_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_1972_ = lean_unsigned_to_nat(0u);
v___x_1973_ = lean_unsigned_to_nat(1u);
v___x_1974_ = l_Lean_Syntax_getArg(v_x_1963_, v___x_1973_);
lean_dec(v_x_1963_);
v_kvs_1975_ = l_Lean_Syntax_getArgs(v___x_1974_);
lean_dec(v___x_1974_);
v_t_1998_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5);
v___x_1999_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_kvs_1975_);
lean_dec_ref(v_kvs_1975_);
v___x_2000_ = lean_array_get_size(v___x_1999_);
v___x_2001_ = lean_nat_dec_lt(v___x_1972_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_dec_ref(v___x_1999_);
lean_dec_ref(v_elabVal_1964_);
v_a_1977_ = v_t_1998_;
goto v___jp_1976_;
}
else
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_nat_dec_le(v___x_2000_, v___x_2000_);
if (v___x_2002_ == 0)
{
if (v___x_2001_ == 0)
{
lean_dec_ref(v___x_1999_);
lean_dec_ref(v_elabVal_1964_);
v_a_1977_ = v_t_1998_;
goto v___jp_1976_;
}
else
{
size_t v___x_2003_; size_t v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = ((size_t)0ULL);
v___x_2004_ = lean_usize_of_nat(v___x_2000_);
v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1964_, v___x_1999_, v___x_2003_, v___x_2004_, v_t_1998_, v_a_1965_, v_a_1966_);
lean_dec_ref(v___x_1999_);
v___y_1988_ = v___x_2005_;
goto v___jp_1987_;
}
}
else
{
size_t v___x_2006_; size_t v___x_2007_; lean_object* v___x_2008_; 
v___x_2006_ = ((size_t)0ULL);
v___x_2007_ = lean_usize_of_nat(v___x_2000_);
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1964_, v___x_1999_, v___x_2006_, v___x_2007_, v_t_1998_, v_a_1965_, v_a_1966_);
lean_dec_ref(v___x_1999_);
v___y_1988_ = v___x_2008_;
goto v___jp_1987_;
}
}
v___jp_1976_:
{
lean_object* v_items_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v_items_1978_ = lean_ctor_get(v_a_1977_, 0);
lean_inc_ref(v_items_1978_);
lean_dec_ref(v_a_1977_);
v___x_1979_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
v___x_1980_ = lean_array_get_size(v_items_1978_);
v___x_1981_ = lean_nat_dec_lt(v___x_1972_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_dec_ref(v_items_1978_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1979_);
return v___x_1982_;
}
else
{
size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1983_ = ((size_t)0ULL);
v___x_1984_ = lean_usize_of_nat(v___x_1980_);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_1978_, v___x_1983_, v___x_1984_, v___x_1979_);
lean_dec_ref(v_items_1978_);
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
return v___x_1986_;
}
}
v___jp_1987_:
{
if (lean_obj_tag(v___y_1988_) == 0)
{
lean_object* v_a_1989_; 
v_a_1989_ = lean_ctor_get(v___y_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___y_1988_, 1);
v_a_1977_ = v_a_1989_;
goto v___jp_1976_;
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_a_1990_ = lean_ctor_get(v___y_1988_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___y_1988_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___y_1988_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___y_1988_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object* v_x_2009_, lean_object* v_elabVal_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2009_, v_elabVal_2010_, v_a_2011_, v_a_2012_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(lean_object* v_00_u03b1_2015_, lean_object* v_ref_2016_, lean_object* v_msg_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v_ref_2016_, v_msg_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object* v_00_u03b1_2023_, lean_object* v_ref_2024_, lean_object* v_msg_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_00_u03b1_2023_, v_ref_2024_, v_msg_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v_ref_2024_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(lean_object* v_00_u03b1_2031_, lean_object* v_msg_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_2032_, v___y_2034_, v___y_2035_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2038_, lean_object* v_msg_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(v_00_u03b1_2038_, v_msg_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2044_;
}
}
static lean_object* _init_l_Lake_Toml_elabVal___closed__1(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l_Lake_Toml_elabVal___closed__0));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object* v_x_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lake_Toml_elabVal(v_x_2048_, v_a_2049_, v_a_2050_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object* v_x_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
lean_inc(v_x_2053_);
v___x_2058_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; uint8_t v___x_2060_; 
v___x_2059_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
lean_inc(v_x_2053_);
v___x_2060_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; uint8_t v___x_2062_; 
v___x_2061_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
lean_inc(v_x_2053_);
v___x_2062_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2061_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2063_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
lean_inc(v_x_2053_);
v___x_2064_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
lean_inc(v_x_2053_);
v___x_2066_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
lean_inc(v_x_2053_);
v___x_2068_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_2053_);
v___x_2070_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; uint8_t v___x_2072_; 
v___x_2071_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_2053_);
v___x_2072_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_2053_);
v___x_2074_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2053_);
v___x_2076_ = l_Lean_Syntax_isOfKind(v_x_2053_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_obj_once(&l_Lake_Toml_elabVal___closed__1, &l_Lake_Toml_elabVal___closed__1_once, _init_l_Lake_Toml_elabVal___closed__1);
v___x_2078_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2053_, v___x_2077_, v_a_2054_, v_a_2055_);
lean_dec(v_x_2053_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2053_);
v___x_2080_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2053_, v___x_2079_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2089_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2089_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2089_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2085_, 0, v_x_2053_);
lean_ctor_set(v___x_2085_, 1, v_a_2081_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2085_);
v___x_2087_ = v___x_2083_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
lean_dec(v_x_2053_);
v_a_2090_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2080_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2080_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2053_);
v___x_2099_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_2053_, v___x_2098_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2108_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2104_, 0, v_x_2053_);
lean_ctor_set(v___x_2104_, 1, v_a_2100_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_x_2053_);
v_a_2109_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2099_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2099_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
else
{
lean_object* v___x_2117_; 
lean_inc(v_x_2053_);
v___x_2117_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2127_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2127_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2127_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2125_; 
v___x_2122_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_2122_, 0, v_x_2053_);
v___x_2123_ = lean_unbox(v_a_2118_);
lean_dec(v_a_2118_);
lean_ctor_set_uint8(v___x_2122_, sizeof(void*)*1, v___x_2123_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2122_);
v___x_2125_ = v___x_2120_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2122_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v_x_2053_);
v_a_2128_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2117_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2117_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
else
{
lean_object* v___x_2136_; 
lean_inc(v_x_2053_);
v___x_2136_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2145_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2145_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2145_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v_x_2053_);
lean_ctor_set(v___x_2141_, 1, v_a_2137_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2141_);
v___x_2143_ = v___x_2139_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_x_2053_);
v_a_2146_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2136_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2136_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
else
{
lean_object* v___x_2154_; 
v___x_2154_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2163_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2159_, 0, v_x_2053_);
lean_ctor_set(v___x_2159_, 1, v_a_2155_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2159_);
v___x_2161_ = v___x_2157_;
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
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_x_2053_);
v_a_2164_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2154_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2154_);
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
else
{
lean_object* v___x_2172_; 
v___x_2172_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2182_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2177_ = lean_nat_to_int(v_a_2173_);
v___x_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2178_, 0, v_x_2053_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec(v_x_2053_);
v_a_2183_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2172_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2172_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
else
{
lean_object* v___x_2191_; 
v___x_2191_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2201_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2201_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2201_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2196_ = lean_nat_to_int(v_a_2192_);
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_x_2053_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2197_);
v___x_2199_ = v___x_2194_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_x_2053_);
v_a_2202_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2191_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2191_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_object* v___x_2210_; 
v___x_2210_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2220_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2220_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2220_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2215_ = lean_nat_to_int(v_a_2211_);
v___x_2216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_x_2053_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2216_);
v___x_2218_ = v___x_2213_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec(v_x_2053_);
v_a_2221_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2210_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2210_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v___x_2229_; 
v___x_2229_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2238_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_x_2053_);
lean_ctor_set(v___x_2234_, 1, v_a_2230_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_x_2053_);
v_a_2239_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2229_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2229_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
else
{
lean_object* v___x_2247_; 
v___x_2247_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_2053_, v_a_2054_, v_a_2055_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2257_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2250_ = v___x_2247_;
v_isShared_2251_ = v_isSharedCheck_2257_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2257_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; double v___x_2253_; lean_object* v___x_2255_; 
v___x_2252_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_2252_, 0, v_x_2053_);
v___x_2253_ = lean_unbox_float(v_a_2248_);
lean_dec(v_a_2248_);
lean_ctor_set_float(v___x_2252_, sizeof(void*)*1, v___x_2253_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2252_);
v___x_2255_ = v___x_2250_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2252_);
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
lean_object* v_a_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2265_; 
lean_dec(v_x_2053_);
v_a_2258_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2260_ = v___x_2247_;
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_a_2258_);
lean_dec(v___x_2247_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2265_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2263_; 
if (v_isShared_2261_ == 0)
{
v___x_2263_ = v___x_2260_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2258_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
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
