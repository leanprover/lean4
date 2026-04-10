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
lean_dec_ref(v___x_34_);
lean_dec_ref(v___x_29_);
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
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_231__overap_50_; lean_object* v___x_51_; 
lean_dec(v___x_35_);
v___x_44_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4));
v___x_45_ = lean_string_append(v___x_44_, v_name_10_);
v___x_46_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5));
v___x_47_ = lean_string_append(v___x_45_, v___x_46_);
v___x_48_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
v___x_49_ = l_Lean_MessageData_ofFormat(v___x_48_);
v___x_231__overap_50_ = l_Lean_throwErrorAt___redArg(v___x_29_, v___x_34_, v_x_9_, v___x_49_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
v___x_51_ = lean_apply_3(v___x_231__overap_50_, v_a_11_, v_a_12_, lean_box(0));
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
v___x_64_ = lean_alloc_ctor(0, 10, 0);
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
lean_dec_ref(v___x_137_);
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
lean_object* v_startInclusive_220_; lean_object* v_endExclusive_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_startInclusive_220_ = lean_ctor_get(v___x_216_, 1);
v_endExclusive_221_ = lean_ctor_get(v___x_216_, 2);
v___x_222_ = lean_nat_sub(v_endExclusive_221_, v_startInclusive_220_);
v___x_223_ = lean_nat_dec_eq(v_a_218_, v___x_222_);
lean_dec(v___x_222_);
if (v___x_223_ == 0)
{
uint32_t v___x_224_; lean_object* v___x_225_; uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_224_ = lean_string_utf8_get_fast(v_s_217_, v_a_218_);
v___x_225_ = lean_string_utf8_next_fast(v_s_217_, v_a_218_);
lean_dec(v_a_218_);
v___x_226_ = 95;
v___x_227_ = lean_uint32_dec_eq(v___x_224_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; uint32_t v___x_230_; uint32_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_228_ = lean_unsigned_to_nat(10u);
v___x_229_ = lean_nat_mul(v_b_219_, v___x_228_);
lean_dec(v_b_219_);
v___x_230_ = 48;
v___x_231_ = lean_uint32_sub(v___x_224_, v___x_230_);
v___x_232_ = lean_uint32_to_nat(v___x_231_);
v___x_233_ = lean_nat_add(v___x_229_, v___x_232_);
lean_dec(v___x_232_);
lean_dec(v___x_229_);
v_a_218_ = v___x_225_;
v_b_219_ = v___x_233_;
goto _start;
}
else
{
v_a_218_ = v___x_225_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object* v___x_236_, lean_object* v_s_237_, lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_236_, v_s_237_, v_a_238_, v_b_239_);
lean_dec_ref(v_s_237_);
lean_dec_ref(v___x_236_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object* v_s_241_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_string_utf8_byte_size(v_s_241_);
lean_inc_ref(v_s_241_);
v___x_244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_244_, 0, v_s_241_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
lean_ctor_set(v___x_244_, 2, v___x_243_);
v___x_245_ = l_String_Slice_positions(v___x_244_);
v___x_246_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_244_, v_s_241_, v___x_245_, v___x_242_);
lean_dec_ref(v_s_241_);
lean_dec_ref(v___x_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object* v___x_247_, lean_object* v_s_248_, lean_object* v_inst_249_, lean_object* v_R_250_, lean_object* v_a_251_, lean_object* v_b_252_, lean_object* v_c_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_247_, v_s_248_, v_a_251_, v_b_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object* v___x_255_, lean_object* v_s_256_, lean_object* v_inst_257_, lean_object* v_R_258_, lean_object* v_a_259_, lean_object* v_b_260_, lean_object* v_c_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(v___x_255_, v_s_256_, v_inst_257_, v_R_258_, v_a_259_, v_b_260_, v_c_261_);
lean_dec_ref(v_s_256_);
lean_dec_ref(v___x_255_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object* v_s_263_){
_start:
{
uint32_t v___y_265_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_string_utf8_byte_size(v_s_263_);
lean_inc_ref(v_s_263_);
v___x_290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_290_, 0, v_s_263_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
lean_ctor_set(v___x_290_, 2, v___x_289_);
v___x_291_ = l_String_Slice_Pos_get_x3f(v___x_290_, v___x_288_);
lean_dec_ref(v___x_290_);
if (lean_obj_tag(v___x_291_) == 0)
{
uint32_t v___x_292_; 
v___x_292_ = 65;
v___y_265_ = v___x_292_;
goto v___jp_264_;
}
else
{
lean_object* v_val_293_; uint32_t v___x_294_; 
v_val_293_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_val_293_);
lean_dec_ref(v___x_291_);
v___x_294_ = lean_unbox_uint32(v_val_293_);
lean_dec(v_val_293_);
v___y_265_ = v___x_294_;
goto v___jp_264_;
}
v___jp_264_:
{
uint32_t v___x_266_; uint8_t v___x_267_; 
v___x_266_ = 45;
v___x_267_ = lean_uint32_dec_eq(v___y_265_, v___x_266_);
if (v___x_267_ == 0)
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 43;
v___x_269_ = lean_uint32_dec_eq(v___y_265_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_box(v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v_s_263_);
return v___x_271_;
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_string_utf8_byte_size(v_s_263_);
lean_inc_ref(v_s_263_);
v___x_275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_275_, 0, v_s_263_);
lean_ctor_set(v___x_275_, 1, v___x_273_);
lean_ctor_set(v___x_275_, 2, v___x_274_);
v___x_276_ = l_String_Slice_Pos_nextn(v___x_275_, v___x_273_, v___x_272_);
lean_dec_ref(v___x_275_);
v___x_277_ = lean_string_utf8_extract(v_s_263_, v___x_276_, v___x_274_);
lean_dec(v___x_276_);
lean_dec_ref(v_s_263_);
v___x_278_ = lean_box(v___x_267_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
return v___x_279_;
}
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_string_utf8_byte_size(v_s_263_);
lean_inc_ref(v_s_263_);
v___x_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_283_, 0, v_s_263_);
lean_ctor_set(v___x_283_, 1, v___x_281_);
lean_ctor_set(v___x_283_, 2, v___x_282_);
v___x_284_ = l_String_Slice_Pos_nextn(v___x_283_, v___x_281_, v___x_280_);
lean_dec_ref(v___x_283_);
v___x_285_ = lean_string_utf8_extract(v_s_263_, v___x_284_, v___x_282_);
lean_dec(v___x_284_);
lean_dec_ref(v_s_263_);
v___x_286_ = lean_box(v___x_267_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_285_);
return v___x_287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object* v_s_295_){
_start:
{
uint8_t v_fst_297_; lean_object* v_snd_298_; uint32_t v___y_304_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_string_utf8_byte_size(v_s_295_);
lean_inc_ref(v_s_295_);
v___x_323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_323_, 0, v_s_295_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
lean_ctor_set(v___x_323_, 2, v___x_322_);
v___x_324_ = l_String_Slice_Pos_get_x3f(v___x_323_, v___x_321_);
lean_dec_ref(v___x_323_);
if (lean_obj_tag(v___x_324_) == 0)
{
uint32_t v___x_325_; 
v___x_325_ = 65;
v___y_304_ = v___x_325_;
goto v___jp_303_;
}
else
{
lean_object* v_val_326_; uint32_t v___x_327_; 
v_val_326_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_326_);
lean_dec_ref(v___x_324_);
v___x_327_ = lean_unbox_uint32(v_val_326_);
lean_dec(v_val_326_);
v___y_304_ = v___x_327_;
goto v___jp_303_;
}
v___jp_296_:
{
if (v_fst_297_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_298_);
v___x_300_ = lean_nat_to_int(v___x_299_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_298_);
v___x_302_ = l_Int_negOfNat(v___x_301_);
lean_dec(v___x_301_);
return v___x_302_;
}
}
v___jp_303_:
{
uint32_t v___x_305_; uint8_t v___x_306_; 
v___x_305_ = 45;
v___x_306_ = lean_uint32_dec_eq(v___y_304_, v___x_305_);
if (v___x_306_ == 0)
{
uint32_t v___x_307_; uint8_t v___x_308_; 
v___x_307_ = 43;
v___x_308_ = lean_uint32_dec_eq(v___y_304_, v___x_307_);
if (v___x_308_ == 0)
{
v_fst_297_ = v___x_308_;
v_snd_298_ = v_s_295_;
goto v___jp_296_;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_string_utf8_byte_size(v_s_295_);
lean_inc_ref(v_s_295_);
v___x_312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_312_, 0, v_s_295_);
lean_ctor_set(v___x_312_, 1, v___x_310_);
lean_ctor_set(v___x_312_, 2, v___x_311_);
v___x_313_ = l_String_Slice_Pos_nextn(v___x_312_, v___x_310_, v___x_309_);
lean_dec_ref(v___x_312_);
v___x_314_ = lean_string_utf8_extract(v_s_295_, v___x_313_, v___x_311_);
lean_dec(v___x_313_);
lean_dec_ref(v_s_295_);
v_fst_297_ = v___x_306_;
v_snd_298_ = v___x_314_;
goto v___jp_296_;
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_string_utf8_byte_size(v_s_295_);
lean_inc_ref(v_s_295_);
v___x_318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_318_, 0, v_s_295_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
v___x_319_ = l_String_Slice_Pos_nextn(v___x_318_, v___x_316_, v___x_315_);
lean_dec_ref(v___x_318_);
v___x_320_ = lean_string_utf8_extract(v_s_295_, v___x_319_, v___x_317_);
lean_dec(v___x_319_);
lean_dec_ref(v_s_295_);
v_fst_297_ = v___x_306_;
v_snd_298_ = v___x_320_;
goto v___jp_296_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3));
v___x_337_ = l_Lean_MessageData_ofFormat(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object* v_x_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_a_343_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
v___x_347_ = l_Lean_Syntax_isLit_x3f(v___x_346_, v_x_338_);
if (lean_obj_tag(v___x_347_) == 1)
{
lean_object* v_val_348_; 
v_val_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_val_348_);
lean_dec_ref(v___x_347_);
v_a_343_ = v_val_348_;
goto v___jp_342_;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec(v___x_347_);
v___x_349_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4);
v___x_350_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_338_, v___x_349_, v_a_339_, v_a_340_);
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_a_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object* v_x_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_359_, v_a_360_, v_a_361_);
lean_dec(v_a_361_);
lean_dec_ref(v_a_360_);
lean_dec(v_x_359_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object* v___x_364_, lean_object* v_s_365_, lean_object* v_a_366_, lean_object* v_b_367_){
_start:
{
lean_object* v_startInclusive_368_; lean_object* v_endExclusive_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_startInclusive_368_ = lean_ctor_get(v___x_364_, 1);
v_endExclusive_369_ = lean_ctor_get(v___x_364_, 2);
v___x_370_ = lean_nat_sub(v_endExclusive_369_, v_startInclusive_368_);
v___x_371_ = lean_nat_dec_eq(v_a_366_, v___x_370_);
lean_dec(v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v_fst_372_; lean_object* v_snd_373_; uint32_t v___x_374_; lean_object* v___x_375_; uint32_t v___x_376_; uint8_t v___x_377_; 
v_fst_372_ = lean_ctor_get(v_b_367_, 0);
v_snd_373_ = lean_ctor_get(v_b_367_, 1);
v___x_374_ = lean_string_utf8_get_fast(v_s_365_, v_a_366_);
v___x_375_ = lean_string_utf8_next_fast(v_s_365_, v_a_366_);
lean_dec(v_a_366_);
v___x_376_ = 95;
v___x_377_ = lean_uint32_dec_eq(v___x_374_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_400_; 
lean_inc(v_snd_373_);
lean_inc(v_fst_372_);
v_isSharedCheck_400_ = !lean_is_exclusive(v_b_367_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; lean_object* v_unused_402_; 
v_unused_401_ = lean_ctor_get(v_b_367_, 1);
lean_dec(v_unused_401_);
v_unused_402_ = lean_ctor_get(v_b_367_, 0);
lean_dec(v_unused_402_);
v___x_379_ = v_b_367_;
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
else
{
lean_dec(v_b_367_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_381_ = 46;
v___x_382_ = lean_uint32_dec_eq(v___x_374_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; uint32_t v___x_385_; uint32_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_383_ = lean_unsigned_to_nat(10u);
v___x_384_ = lean_nat_mul(v_fst_372_, v___x_383_);
lean_dec(v_fst_372_);
v___x_385_ = 48;
v___x_386_ = lean_uint32_sub(v___x_374_, v___x_385_);
v___x_387_ = lean_uint32_to_nat(v___x_386_);
v___x_388_ = lean_nat_add(v___x_384_, v___x_387_);
lean_dec(v___x_387_);
lean_dec(v___x_384_);
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_snd_373_, v___x_389_);
lean_dec(v_snd_373_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___x_390_);
lean_ctor_set(v___x_379_, 0, v___x_388_);
v___x_392_ = v___x_379_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___x_390_);
v___x_392_ = v_reuseFailAlloc_394_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
v_a_366_ = v___x_375_;
v_b_367_ = v___x_392_;
goto _start;
}
}
else
{
lean_object* v___x_395_; lean_object* v___x_397_; 
lean_dec(v_snd_373_);
v___x_395_ = lean_unsigned_to_nat(0u);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___x_395_);
v___x_397_ = v___x_379_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_fst_372_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_395_);
v___x_397_ = v_reuseFailAlloc_399_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
v_a_366_ = v___x_375_;
v_b_367_ = v___x_397_;
goto _start;
}
}
}
}
else
{
v_a_366_ = v___x_375_;
goto _start;
}
}
else
{
lean_dec(v_a_366_);
return v_b_367_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object* v___x_404_, lean_object* v_s_405_, lean_object* v_a_406_, lean_object* v_b_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_404_, v_s_405_, v_a_406_, v_b_407_);
lean_dec_ref(v_s_405_);
lean_dec_ref(v___x_404_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object* v_s_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_fst_417_; lean_object* v_snd_418_; uint8_t v___x_419_; 
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_string_length(v_s_409_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = lean_string_utf8_byte_size(v_s_409_);
lean_inc_ref(v_s_409_);
v___x_414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_414_, 0, v_s_409_);
lean_ctor_set(v___x_414_, 1, v___x_410_);
lean_ctor_set(v___x_414_, 2, v___x_413_);
v___x_415_ = l_String_Slice_positions(v___x_414_);
v___x_416_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_414_, v_s_409_, v___x_415_, v___x_412_);
lean_dec_ref(v_s_409_);
lean_dec_ref(v___x_414_);
v_fst_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_fst_417_);
v_snd_418_ = lean_ctor_get(v___x_416_, 1);
lean_inc(v_snd_418_);
v___x_419_ = lean_nat_dec_le(v___x_411_, v_snd_418_);
lean_dec(v_snd_418_);
if (v___x_419_ == 0)
{
lean_dec(v_fst_417_);
return v___x_416_;
}
else
{
lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; lean_object* v_unused_428_; 
v_unused_427_ = lean_ctor_get(v___x_416_, 1);
lean_dec(v_unused_427_);
v_unused_428_ = lean_ctor_get(v___x_416_, 0);
lean_dec(v_unused_428_);
v___x_421_ = v___x_416_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_dec(v___x_416_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_410_);
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_fst_417_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_410_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object* v___x_429_, lean_object* v_s_430_, lean_object* v_inst_431_, lean_object* v_R_432_, lean_object* v_a_433_, lean_object* v_b_434_, lean_object* v_c_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_429_, v_s_430_, v_a_433_, v_b_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object* v___x_437_, lean_object* v_s_438_, lean_object* v_inst_439_, lean_object* v_R_440_, lean_object* v_a_441_, lean_object* v_b_442_, lean_object* v_c_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(v___x_437_, v_s_438_, v_inst_439_, v_R_440_, v_a_441_, v_b_442_, v_c_443_);
lean_dec_ref(v_s_438_);
lean_dec_ref(v___x_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object* v_s_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0));
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object* v_s_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v_s_449_);
lean_dec_ref(v_s_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object* v_s_451_, lean_object* v___x_452_, lean_object* v___x_453_, lean_object* v_a_454_, lean_object* v_b_455_){
_start:
{
lean_object* v_it_457_; lean_object* v_startInclusive_458_; lean_object* v_endExclusive_459_; 
if (lean_obj_tag(v_a_454_) == 0)
{
lean_object* v_currPos_464_; lean_object* v_searcher_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_495_; 
v_currPos_464_ = lean_ctor_get(v_a_454_, 0);
v_searcher_465_ = lean_ctor_get(v_a_454_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_a_454_);
if (v_isSharedCheck_495_ == 0)
{
v___x_467_ = v_a_454_;
v_isShared_468_ = v_isSharedCheck_495_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_searcher_465_);
lean_inc(v_currPos_464_);
lean_dec(v_a_454_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_495_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
uint8_t v___y_470_; lean_object* v_startInclusive_485_; lean_object* v_endExclusive_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_startInclusive_485_ = lean_ctor_get(v___x_452_, 1);
v_endExclusive_486_ = lean_ctor_get(v___x_452_, 2);
v___x_487_ = lean_nat_sub(v_endExclusive_486_, v_startInclusive_485_);
v___x_488_ = lean_nat_dec_eq(v_searcher_465_, v___x_487_);
lean_dec(v___x_487_);
if (v___x_488_ == 0)
{
uint32_t v___x_489_; uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_489_ = lean_string_utf8_get_fast(v_s_451_, v_searcher_465_);
v___x_490_ = 69;
v___x_491_ = lean_uint32_dec_eq(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
uint32_t v___x_492_; uint8_t v___x_493_; 
v___x_492_ = 101;
v___x_493_ = lean_uint32_dec_eq(v___x_489_, v___x_492_);
v___y_470_ = v___x_493_;
goto v___jp_469_;
}
else
{
v___y_470_ = v___x_491_;
goto v___jp_469_;
}
}
else
{
lean_object* v___x_494_; 
lean_del_object(v___x_467_);
lean_dec(v_searcher_465_);
v___x_494_ = lean_box(1);
lean_inc(v___x_453_);
v_it_457_ = v___x_494_;
v_startInclusive_458_ = v_currPos_464_;
v_endExclusive_459_ = v___x_453_;
goto v___jp_456_;
}
v___jp_469_:
{
if (v___y_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_string_utf8_next_fast(v_s_451_, v_searcher_465_);
lean_dec(v_searcher_465_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v___x_471_);
v___x_473_ = v___x_467_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_currPos_464_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_475_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
v_a_454_ = v___x_473_;
goto _start;
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v_slice_479_; lean_object* v_nextIt_481_; 
v___x_476_ = lean_string_utf8_next_fast(v_s_451_, v_searcher_465_);
v___x_477_ = lean_nat_sub(v___x_476_, v_searcher_465_);
v___x_478_ = lean_nat_add(v_searcher_465_, v___x_477_);
lean_dec(v___x_477_);
v_slice_479_ = l_String_Slice_subslice_x21(v___x_452_, v_currPos_464_, v_searcher_465_);
lean_inc(v___x_478_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 1, v___x_478_);
lean_ctor_set(v___x_467_, 0, v___x_478_);
v_nextIt_481_ = v___x_467_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_478_);
v_nextIt_481_ = v_reuseFailAlloc_484_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v_startInclusive_482_; lean_object* v_endExclusive_483_; 
v_startInclusive_482_ = lean_ctor_get(v_slice_479_, 0);
lean_inc(v_startInclusive_482_);
v_endExclusive_483_ = lean_ctor_get(v_slice_479_, 1);
lean_inc(v_endExclusive_483_);
lean_dec_ref(v_slice_479_);
v_it_457_ = v_nextIt_481_;
v_startInclusive_458_ = v_startInclusive_482_;
v_endExclusive_459_ = v_endExclusive_483_;
goto v___jp_456_;
}
}
}
}
}
else
{
lean_dec(v___x_453_);
lean_dec_ref(v_s_451_);
return v_b_455_;
}
v___jp_456_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_inc_ref(v_s_451_);
v___x_460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_460_, 0, v_s_451_);
lean_ctor_set(v___x_460_, 1, v_startInclusive_458_);
lean_ctor_set(v___x_460_, 2, v_endExclusive_459_);
v___x_461_ = l_String_Slice_toString(v___x_460_);
lean_dec_ref(v___x_460_);
v___x_462_ = lean_array_push(v_b_455_, v___x_461_);
v_a_454_ = v_it_457_;
v_b_455_ = v___x_462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object* v_s_496_, lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v_a_499_, lean_object* v_b_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_496_, v___x_497_, v___x_498_, v_a_499_, v_b_500_);
lean_dec_ref(v___x_497_);
return v_res_501_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_nat_to_int(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object* v_s_509_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_string_utf8_byte_size(v_s_509_);
lean_inc_ref(v_s_509_);
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v_s_509_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
lean_ctor_set(v___x_514_, 2, v___x_513_);
v___x_515_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v___x_514_);
v___x_516_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2));
v___x_517_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_509_, v___x_514_, v___x_513_, v___x_515_, v___x_516_);
lean_dec_ref(v___x_514_);
v___x_518_ = lean_array_to_list(v___x_517_);
if (lean_obj_tag(v___x_518_) == 1)
{
lean_object* v_tail_519_; 
v_tail_519_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_tail_519_);
if (lean_obj_tag(v_tail_519_) == 0)
{
lean_object* v_head_520_; lean_object* v___x_521_; lean_object* v_fst_522_; lean_object* v_snd_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_531_; 
v_head_520_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_head_520_);
lean_dec_ref(v___x_518_);
v___x_521_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_520_);
v_fst_522_ = lean_ctor_get(v___x_521_, 0);
v_snd_523_ = lean_ctor_get(v___x_521_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_531_ == 0)
{
v___x_525_ = v___x_521_;
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_snd_523_);
lean_inc(v_fst_522_);
lean_dec(v___x_521_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_531_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = l_Int_negOfNat(v_snd_523_);
lean_dec(v_snd_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v___x_527_);
v___x_529_ = v___x_525_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fst_522_);
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
lean_object* v_tail_532_; 
v_tail_532_ = lean_ctor_get(v_tail_519_, 1);
if (lean_obj_tag(v_tail_532_) == 0)
{
lean_object* v_head_533_; lean_object* v_head_534_; lean_object* v___x_535_; lean_object* v_fst_536_; lean_object* v_snd_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_547_; 
v_head_533_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_head_533_);
lean_dec_ref(v___x_518_);
v_head_534_ = lean_ctor_get(v_tail_519_, 0);
lean_inc(v_head_534_);
lean_dec_ref(v_tail_519_);
v___x_535_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_533_);
v_fst_536_ = lean_ctor_get(v___x_535_, 0);
v_snd_537_ = lean_ctor_get(v___x_535_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_547_ == 0)
{
v___x_539_ = v___x_535_;
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snd_537_);
lean_inc(v_fst_536_);
lean_dec(v___x_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_exp_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v_exp_541_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_head_534_);
v___x_542_ = l_Int_negOfNat(v_snd_537_);
lean_dec(v_snd_537_);
v___x_543_ = lean_int_add(v___x_542_, v_exp_541_);
lean_dec(v_exp_541_);
lean_dec(v___x_542_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_543_);
v___x_545_ = v___x_539_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_fst_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
lean_dec_ref(v_tail_519_);
lean_dec_ref(v___x_518_);
goto v___jp_510_;
}
}
}
else
{
lean_dec(v___x_518_);
goto v___jp_510_;
}
v___jp_510_:
{
lean_object* v___x_511_; 
v___x_511_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object* v_s_548_, lean_object* v___x_549_, lean_object* v___x_550_, lean_object* v_inst_551_, lean_object* v_R_552_, lean_object* v_a_553_, lean_object* v_b_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_548_, v___x_549_, v___x_550_, v_a_553_, v_b_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object* v_s_556_, lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v_inst_559_, lean_object* v_R_560_, lean_object* v_a_561_, lean_object* v_b_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(v_s_556_, v___x_557_, v___x_558_, v_inst_559_, v_R_560_, v_a_561_, v_b_562_);
lean_dec_ref(v___x_557_);
return v_res_563_;
}
}
static double _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2(void){
_start:
{
lean_object* v___x_566_; double v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_float_of_nat(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object* v_s_568_){
_start:
{
lean_object* v___x_569_; lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_569_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(v_s_568_);
v_fst_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_fst_570_);
v_snd_571_ = lean_ctor_get(v___x_569_, 1);
lean_inc(v_snd_571_);
lean_dec_ref(v___x_569_);
v___x_572_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0));
v___x_573_ = lean_string_dec_eq(v_snd_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1));
v___x_575_ = lean_string_dec_eq(v_snd_571_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v_fst_577_; lean_object* v_snd_578_; lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; double v_flt_582_; uint8_t v___x_583_; 
v___x_576_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(v_snd_571_);
v_fst_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v___x_576_, 1);
lean_inc(v_snd_578_);
lean_dec_ref(v___x_576_);
v___x_579_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_580_ = lean_int_dec_lt(v_snd_578_, v___x_579_);
v___x_581_ = lean_nat_abs(v_snd_578_);
lean_dec(v_snd_578_);
v_flt_582_ = l_Float_ofScientific(v_fst_577_, v___x_580_, v___x_581_);
lean_dec(v_fst_577_);
v___x_583_ = lean_unbox(v_fst_570_);
lean_dec(v_fst_570_);
if (v___x_583_ == 0)
{
return v_flt_582_;
}
else
{
double v___x_584_; 
v___x_584_ = lean_float_negate(v_flt_582_);
return v___x_584_;
}
}
else
{
uint8_t v___x_585_; 
lean_dec(v_snd_571_);
v___x_585_ = lean_unbox(v_fst_570_);
lean_dec(v_fst_570_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; double v___x_588_; double v___x_589_; double v___x_590_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_unsigned_to_nat(1u);
v___x_588_ = l_Float_ofScientific(v___x_586_, v___x_575_, v___x_587_);
v___x_589_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_590_ = lean_float_div(v___x_588_, v___x_589_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; double v___x_593_; double v___x_594_; double v___x_595_; double v___x_596_; 
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = l_Float_ofScientific(v___x_591_, v___x_575_, v___x_592_);
v___x_594_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_595_ = lean_float_div(v___x_593_, v___x_594_);
v___x_596_ = lean_float_negate(v___x_595_);
return v___x_596_;
}
}
}
else
{
uint8_t v___x_597_; 
lean_dec(v_snd_571_);
v___x_597_ = lean_unbox(v_fst_570_);
lean_dec(v_fst_570_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; double v___x_600_; double v___x_601_; double v___x_602_; 
v___x_598_ = lean_unsigned_to_nat(10u);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = l_Float_ofScientific(v___x_598_, v___x_573_, v___x_599_);
v___x_601_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_602_ = lean_float_div(v___x_600_, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; double v___x_605_; double v___x_606_; double v___x_607_; double v___x_608_; 
v___x_603_ = lean_unsigned_to_nat(10u);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = l_Float_ofScientific(v___x_603_, v___x_573_, v___x_604_);
v___x_606_ = lean_float_negate(v___x_605_);
v___x_607_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_608_ = lean_float_div(v___x_606_, v___x_607_);
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object* v_s_609_){
_start:
{
double v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_s_609_);
v_r_611_ = lean_box_float(v_res_610_);
return v_r_611_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3));
v___x_621_ = l_Lean_MessageData_ofFormat(v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object* v_x_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_a_627_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
v___x_632_ = l_Lean_Syntax_isLit_x3f(v___x_631_, v_x_622_);
if (lean_obj_tag(v___x_632_) == 1)
{
lean_object* v_val_633_; 
v_val_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_val_633_);
lean_dec_ref(v___x_632_);
v_a_627_ = v_val_633_;
goto v___jp_626_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec(v___x_632_);
v___x_634_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4);
v___x_635_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_622_, v___x_634_, v_a_623_, v_a_624_);
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
v___jp_626_:
{
double v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_a_627_);
v___x_629_ = lean_box_float(v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object* v_x_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_x_644_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object* v___x_649_, lean_object* v___x_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_b_653_){
_start:
{
lean_object* v_startInclusive_654_; lean_object* v_endExclusive_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_startInclusive_654_ = lean_ctor_get(v___x_649_, 1);
v_endExclusive_655_ = lean_ctor_get(v___x_649_, 2);
v___x_656_ = lean_nat_sub(v_endExclusive_655_, v_startInclusive_654_);
v___x_657_ = lean_nat_dec_eq(v_a_652_, v___x_656_);
lean_dec(v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint32_t v___x_661_; uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_658_ = lean_nat_add(v___x_650_, v_a_652_);
lean_dec(v_a_652_);
v___x_659_ = lean_string_utf8_next_fast(v_a_651_, v___x_658_);
v___x_660_ = lean_nat_sub(v___x_659_, v___x_650_);
v___x_661_ = lean_string_utf8_get_fast(v_a_651_, v___x_658_);
lean_dec(v___x_658_);
v___x_662_ = 95;
v___x_663_ = lean_uint32_dec_eq(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; uint32_t v___x_666_; uint32_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_664_ = lean_unsigned_to_nat(2u);
v___x_665_ = lean_nat_mul(v_b_653_, v___x_664_);
lean_dec(v_b_653_);
v___x_666_ = 48;
v___x_667_ = lean_uint32_sub(v___x_661_, v___x_666_);
v___x_668_ = lean_uint32_to_nat(v___x_667_);
v___x_669_ = lean_nat_add(v___x_665_, v___x_668_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
v_a_652_ = v___x_660_;
v_b_653_ = v___x_669_;
goto _start;
}
else
{
v_a_652_ = v___x_660_;
goto _start;
}
}
else
{
lean_dec(v_a_652_);
return v_b_653_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object* v___x_672_, lean_object* v___x_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_b_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_672_, v___x_673_, v_a_674_, v_a_675_, v_b_676_);
lean_dec_ref(v_a_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
return v_res_677_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3));
v___x_687_ = l_Lean_MessageData_ofFormat(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object* v_x_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_a_693_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
v___x_704_ = l_Lean_Syntax_isLit_x3f(v___x_703_, v_x_688_);
if (lean_obj_tag(v___x_704_) == 1)
{
lean_object* v_val_705_; 
v_val_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_val_705_);
lean_dec_ref(v___x_704_);
v_a_693_ = v_val_705_;
goto v___jp_692_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v___x_704_);
v___x_706_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4);
v___x_707_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_688_, v___x_706_, v_a_689_, v_a_690_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
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
v___jp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_unsigned_to_nat(2u);
v___x_696_ = lean_string_utf8_byte_size(v_a_693_);
lean_inc_ref_n(v_a_693_, 2);
v___x_697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_697_, 0, v_a_693_);
lean_ctor_set(v___x_697_, 1, v___x_694_);
lean_ctor_set(v___x_697_, 2, v___x_696_);
v___x_698_ = l_String_Slice_Pos_nextn(v___x_697_, v___x_694_, v___x_695_);
lean_dec_ref(v___x_697_);
lean_inc(v___x_698_);
v___x_699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_699_, 0, v_a_693_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
lean_ctor_set(v___x_699_, 2, v___x_696_);
v___x_700_ = l_String_Slice_positions(v___x_699_);
v___x_701_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_699_, v___x_698_, v_a_693_, v___x_700_, v___x_694_);
lean_dec_ref(v_a_693_);
lean_dec(v___x_698_);
lean_dec_ref(v___x_699_);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object* v_x_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_x_716_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v_a_723_, lean_object* v_inst_724_, lean_object* v_R_725_, lean_object* v_a_726_, lean_object* v_b_727_, lean_object* v_c_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_721_, v___x_722_, v_a_723_, v_a_726_, v_b_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v_a_732_, lean_object* v_inst_733_, lean_object* v_R_734_, lean_object* v_a_735_, lean_object* v_b_736_, lean_object* v_c_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(v___x_730_, v___x_731_, v_a_732_, v_inst_733_, v_R_734_, v_a_735_, v_b_736_, v_c_737_);
lean_dec_ref(v_a_732_);
lean_dec(v___x_731_);
lean_dec_ref(v___x_730_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object* v___x_739_, lean_object* v___x_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_b_743_){
_start:
{
lean_object* v_startInclusive_744_; lean_object* v_endExclusive_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_startInclusive_744_ = lean_ctor_get(v___x_739_, 1);
v_endExclusive_745_ = lean_ctor_get(v___x_739_, 2);
v___x_746_ = lean_nat_sub(v_endExclusive_745_, v_startInclusive_744_);
v___x_747_ = lean_nat_dec_eq(v_a_742_, v___x_746_);
lean_dec(v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint32_t v___x_751_; uint32_t v___x_752_; uint8_t v___x_753_; 
v___x_748_ = lean_nat_add(v___x_740_, v_a_742_);
lean_dec(v_a_742_);
v___x_749_ = lean_string_utf8_next_fast(v_a_741_, v___x_748_);
v___x_750_ = lean_nat_sub(v___x_749_, v___x_740_);
v___x_751_ = lean_string_utf8_get_fast(v_a_741_, v___x_748_);
lean_dec(v___x_748_);
v___x_752_ = 95;
v___x_753_ = lean_uint32_dec_eq(v___x_751_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; uint32_t v___x_756_; uint32_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_754_ = lean_unsigned_to_nat(8u);
v___x_755_ = lean_nat_mul(v_b_743_, v___x_754_);
lean_dec(v_b_743_);
v___x_756_ = 48;
v___x_757_ = lean_uint32_sub(v___x_751_, v___x_756_);
v___x_758_ = lean_uint32_to_nat(v___x_757_);
v___x_759_ = lean_nat_add(v___x_755_, v___x_758_);
lean_dec(v___x_758_);
lean_dec(v___x_755_);
v_a_742_ = v___x_750_;
v_b_743_ = v___x_759_;
goto _start;
}
else
{
v_a_742_ = v___x_750_;
goto _start;
}
}
else
{
lean_dec(v_a_742_);
return v_b_743_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object* v___x_762_, lean_object* v___x_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_b_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_762_, v___x_763_, v_a_764_, v_a_765_, v_b_766_);
lean_dec_ref(v_a_764_);
lean_dec(v___x_763_);
lean_dec_ref(v___x_762_);
return v_res_767_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3));
v___x_777_ = l_Lean_MessageData_ofFormat(v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object* v_x_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_a_783_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
v___x_794_ = l_Lean_Syntax_isLit_x3f(v___x_793_, v_x_778_);
if (lean_obj_tag(v___x_794_) == 1)
{
lean_object* v_val_795_; 
v_val_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_val_795_);
lean_dec_ref(v___x_794_);
v_a_783_ = v_val_795_;
goto v___jp_782_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v___x_794_);
v___x_796_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4);
v___x_797_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_778_, v___x_796_, v_a_779_, v_a_780_);
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
v___jp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_unsigned_to_nat(2u);
v___x_786_ = lean_string_utf8_byte_size(v_a_783_);
lean_inc_ref_n(v_a_783_, 2);
v___x_787_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_787_, 0, v_a_783_);
lean_ctor_set(v___x_787_, 1, v___x_784_);
lean_ctor_set(v___x_787_, 2, v___x_786_);
v___x_788_ = l_String_Slice_Pos_nextn(v___x_787_, v___x_784_, v___x_785_);
lean_dec_ref(v___x_787_);
lean_inc(v___x_788_);
v___x_789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_789_, 0, v_a_783_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
lean_ctor_set(v___x_789_, 2, v___x_786_);
v___x_790_ = l_String_Slice_positions(v___x_789_);
v___x_791_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_789_, v___x_788_, v_a_783_, v___x_790_, v___x_784_);
lean_dec_ref(v_a_783_);
lean_dec(v___x_788_);
lean_dec_ref(v___x_789_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object* v_x_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_x_806_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v_a_813_, lean_object* v_inst_814_, lean_object* v_R_815_, lean_object* v_a_816_, lean_object* v_b_817_, lean_object* v_c_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_811_, v___x_812_, v_a_813_, v_a_816_, v_b_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object* v___x_820_, lean_object* v___x_821_, lean_object* v_a_822_, lean_object* v_inst_823_, lean_object* v_R_824_, lean_object* v_a_825_, lean_object* v_b_826_, lean_object* v_c_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(v___x_820_, v___x_821_, v_a_822_, v_inst_823_, v_R_824_, v_a_825_, v_b_826_, v_c_827_);
lean_dec_ref(v_a_822_);
lean_dec(v___x_821_);
lean_dec_ref(v___x_820_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t v_c_829_){
_start:
{
uint32_t v___x_830_; uint8_t v___x_831_; 
v___x_830_ = 57;
v___x_831_ = lean_uint32_dec_le(v_c_829_, v___x_830_);
if (v___x_831_ == 0)
{
uint32_t v___x_832_; uint8_t v___x_833_; 
v___x_832_ = 70;
v___x_833_ = lean_uint32_dec_le(v_c_829_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; uint32_t v___x_835_; uint32_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_834_ = lean_unsigned_to_nat(10u);
v___x_835_ = 97;
v___x_836_ = lean_uint32_sub(v_c_829_, v___x_835_);
v___x_837_ = lean_uint32_to_nat(v___x_836_);
v___x_838_ = lean_nat_add(v___x_834_, v___x_837_);
lean_dec(v___x_837_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; uint32_t v___x_840_; uint32_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_839_ = lean_unsigned_to_nat(10u);
v___x_840_ = 65;
v___x_841_ = lean_uint32_sub(v_c_829_, v___x_840_);
v___x_842_ = lean_uint32_to_nat(v___x_841_);
v___x_843_ = lean_nat_add(v___x_839_, v___x_842_);
lean_dec(v___x_842_);
return v___x_843_;
}
}
else
{
uint32_t v___x_844_; uint32_t v___x_845_; lean_object* v___x_846_; 
v___x_844_ = 48;
v___x_845_ = lean_uint32_sub(v_c_829_, v___x_844_);
v___x_846_ = lean_uint32_to_nat(v___x_845_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object* v_c_847_){
_start:
{
uint32_t v_c_boxed_848_; lean_object* v_res_849_; 
v_c_boxed_848_ = lean_unbox_uint32(v_c_847_);
lean_dec(v_c_847_);
v_res_849_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v_c_boxed_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_b_854_){
_start:
{
lean_object* v_startInclusive_855_; lean_object* v_endExclusive_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_startInclusive_855_ = lean_ctor_get(v___x_850_, 1);
v_endExclusive_856_ = lean_ctor_get(v___x_850_, 2);
v___x_857_ = lean_nat_sub(v_endExclusive_856_, v_startInclusive_855_);
v___x_858_ = lean_nat_dec_eq(v_a_853_, v___x_857_);
lean_dec(v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint32_t v___x_862_; uint32_t v___x_863_; uint8_t v___x_864_; 
v___x_859_ = lean_nat_add(v___x_851_, v_a_853_);
lean_dec(v_a_853_);
v___x_860_ = lean_string_utf8_next_fast(v_a_852_, v___x_859_);
v___x_861_ = lean_nat_sub(v___x_860_, v___x_851_);
v___x_862_ = lean_string_utf8_get_fast(v_a_852_, v___x_859_);
lean_dec(v___x_859_);
v___x_863_ = 95;
v___x_864_ = lean_uint32_dec_eq(v___x_862_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_865_ = lean_unsigned_to_nat(16u);
v___x_866_ = lean_nat_mul(v_b_854_, v___x_865_);
lean_dec(v_b_854_);
v___x_867_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_862_);
v___x_868_ = lean_nat_add(v___x_866_, v___x_867_);
lean_dec(v___x_867_);
lean_dec(v___x_866_);
v_a_853_ = v___x_861_;
v_b_854_ = v___x_868_;
goto _start;
}
else
{
v_a_853_ = v___x_861_;
goto _start;
}
}
else
{
lean_dec(v_a_853_);
return v_b_854_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_b_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_871_, v___x_872_, v_a_873_, v_a_874_, v_b_875_);
lean_dec_ref(v_a_873_);
lean_dec(v___x_872_);
lean_dec_ref(v___x_871_);
return v_res_876_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3));
v___x_886_ = l_Lean_MessageData_ofFormat(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object* v_x_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_a_892_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
v___x_903_ = l_Lean_Syntax_isLit_x3f(v___x_902_, v_x_887_);
if (lean_obj_tag(v___x_903_) == 1)
{
lean_object* v_val_904_; 
v_val_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref(v___x_903_);
v_a_892_ = v_val_904_;
goto v___jp_891_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v___x_903_);
v___x_905_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4);
v___x_906_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_887_, v___x_905_, v_a_888_, v_a_889_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
v___jp_891_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_unsigned_to_nat(2u);
v___x_895_ = lean_string_utf8_byte_size(v_a_892_);
lean_inc_ref_n(v_a_892_, 2);
v___x_896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_896_, 0, v_a_892_);
lean_ctor_set(v___x_896_, 1, v___x_893_);
lean_ctor_set(v___x_896_, 2, v___x_895_);
v___x_897_ = l_String_Slice_Pos_nextn(v___x_896_, v___x_893_, v___x_894_);
lean_dec_ref(v___x_896_);
lean_inc(v___x_897_);
v___x_898_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_898_, 0, v_a_892_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
lean_ctor_set(v___x_898_, 2, v___x_895_);
v___x_899_ = l_String_Slice_positions(v___x_898_);
v___x_900_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_898_, v___x_897_, v_a_892_, v___x_899_, v___x_893_);
lean_dec_ref(v_a_892_);
lean_dec(v___x_897_);
lean_dec_ref(v___x_898_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object* v_x_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_915_, v_a_916_, v_a_917_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_x_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object* v___x_920_, lean_object* v___x_921_, lean_object* v_a_922_, lean_object* v_inst_923_, lean_object* v_R_924_, lean_object* v_a_925_, lean_object* v_b_926_, lean_object* v_c_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_920_, v___x_921_, v_a_922_, v_a_925_, v_b_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object* v___x_929_, lean_object* v___x_930_, lean_object* v_a_931_, lean_object* v_inst_932_, lean_object* v_R_933_, lean_object* v_a_934_, lean_object* v_b_935_, lean_object* v_c_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(v___x_929_, v___x_930_, v_a_931_, v_inst_932_, v_R_933_, v_a_934_, v_b_935_, v_c_936_);
lean_dec_ref(v_a_931_);
lean_dec(v___x_930_);
lean_dec_ref(v___x_929_);
return v_res_937_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5));
v___x_950_ = l_Lean_MessageData_ofFormat(v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object* v_x_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_a_956_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
v___x_969_ = l_Lean_Syntax_isLit_x3f(v___x_968_, v_x_951_);
if (lean_obj_tag(v___x_969_) == 1)
{
lean_object* v_val_970_; 
v_val_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_val_970_);
lean_dec_ref(v___x_969_);
v_a_956_ = v_val_970_;
goto v___jp_955_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v___x_969_);
v___x_971_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6);
v___x_972_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_951_, v___x_971_, v_a_952_, v_a_953_);
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
v___jp_955_:
{
lean_object* v___x_957_; 
v___x_957_ = l_Lake_Toml_DateTime_ofString_x3f(v_a_956_);
if (lean_obj_tag(v___x_957_) == 1)
{
lean_object* v_val_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
v_val_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_val_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 0);
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_val_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v___x_957_);
v___x_966_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1);
v___x_967_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_951_, v___x_966_, v_a_952_, v_a_953_);
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object* v_x_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_x_981_);
return v_res_985_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3));
v___x_995_ = l_Lean_MessageData_ofFormat(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object* v_x_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_a_1001_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
v___x_1014_ = l_Lean_Syntax_isLit_x3f(v___x_1013_, v_x_996_);
if (lean_obj_tag(v___x_1014_) == 1)
{
lean_object* v_val_1015_; 
v_val_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_val_1015_);
lean_dec_ref(v___x_1014_);
v_a_1001_ = v_val_1015_;
goto v___jp_1000_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v___x_1014_);
v___x_1016_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4);
v___x_1017_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_996_, v___x_1016_, v_a_997_, v_a_998_);
return v___x_1017_;
}
v___jp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_string_utf8_byte_size(v_a_1001_);
lean_inc_ref_n(v_a_1001_, 2);
v___x_1005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1005_, 0, v_a_1001_);
lean_ctor_set(v___x_1005_, 1, v___x_1003_);
lean_ctor_set(v___x_1005_, 2, v___x_1004_);
v___x_1006_ = l_String_Slice_Pos_nextn(v___x_1005_, v___x_1003_, v___x_1002_);
lean_dec_ref(v___x_1005_);
lean_inc(v___x_1006_);
v___x_1007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1007_, 0, v_a_1001_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_ctor_set(v___x_1007_, 2, v___x_1004_);
v___x_1008_ = lean_nat_sub(v___x_1004_, v___x_1006_);
v___x_1009_ = l_String_Slice_Pos_prevn(v___x_1007_, v___x_1008_, v___x_1002_);
lean_dec_ref(v___x_1007_);
v___x_1010_ = lean_nat_add(v___x_1006_, v___x_1009_);
lean_dec(v___x_1009_);
v___x_1011_ = lean_string_utf8_extract(v_a_1001_, v___x_1006_, v___x_1010_);
lean_dec(v___x_1010_);
lean_dec(v___x_1006_);
lean_dec_ref(v_a_1001_);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object* v_x_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1018_, v_a_1019_, v_a_1020_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_x_1018_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object* v_msg_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = l_String_instInhabitedSlice;
v___x_1025_ = lean_panic_fn_borrowed(v___x_1024_, v_msg_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object* v___y_1026_, lean_object* v_a_1027_, lean_object* v_b_1028_){
_start:
{
lean_object* v_str_1029_; lean_object* v_startInclusive_1030_; lean_object* v_endExclusive_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_str_1029_ = lean_ctor_get(v___y_1026_, 0);
v_startInclusive_1030_ = lean_ctor_get(v___y_1026_, 1);
v_endExclusive_1031_ = lean_ctor_get(v___y_1026_, 2);
v___x_1032_ = lean_nat_sub(v_endExclusive_1031_, v_startInclusive_1030_);
v___x_1033_ = lean_nat_dec_eq(v_a_1027_, v___x_1032_);
lean_dec(v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; uint32_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1034_ = lean_nat_add(v_startInclusive_1030_, v_a_1027_);
lean_dec(v_a_1027_);
v___x_1035_ = lean_string_utf8_get_fast(v_str_1029_, v___x_1034_);
v___x_1036_ = lean_string_utf8_next_fast(v_str_1029_, v___x_1034_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_nat_sub(v___x_1036_, v_startInclusive_1030_);
v___x_1038_ = lean_unsigned_to_nat(16u);
v___x_1039_ = lean_nat_mul(v_b_1028_, v___x_1038_);
lean_dec(v_b_1028_);
v___x_1040_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_1035_);
v___x_1041_ = lean_nat_add(v___x_1039_, v___x_1040_);
lean_dec(v___x_1040_);
lean_dec(v___x_1039_);
v_a_1027_ = v___x_1037_;
v_b_1028_ = v___x_1041_;
goto _start;
}
else
{
lean_dec(v_a_1027_);
return v_b_1028_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object* v___y_1043_, lean_object* v_a_1044_, lean_object* v_b_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1043_, v_a_1044_, v_b_1045_);
lean_dec_ref(v___y_1043_);
return v_res_1046_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1050_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2));
v___x_1051_ = lean_unsigned_to_nat(14u);
v___x_1052_ = lean_unsigned_to_nat(22u);
v___x_1053_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1));
v___x_1054_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0));
v___x_1055_ = l_mkPanicMessageWithDecl(v___x_1054_, v___x_1053_, v___x_1052_, v___x_1051_, v___x_1050_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object* v_s_1056_){
_start:
{
lean_object* v_str_1057_; lean_object* v_startPos_1058_; lean_object* v_stopPos_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1077_; 
v_str_1057_ = lean_ctor_get(v_s_1056_, 0);
v_startPos_1058_ = lean_ctor_get(v_s_1056_, 1);
v_stopPos_1059_ = lean_ctor_get(v_s_1056_, 2);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_s_1056_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1061_ = v_s_1056_;
v_isShared_1062_ = v_isSharedCheck_1077_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_stopPos_1059_);
lean_inc(v_startPos_1058_);
lean_inc(v_str_1057_);
lean_dec(v_s_1056_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1077_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___y_1065_; uint8_t v___x_1071_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1071_ = lean_string_is_valid_pos(v_str_1057_, v_startPos_1058_);
if (v___x_1071_ == 0)
{
lean_del_object(v___x_1061_);
lean_dec(v_stopPos_1059_);
lean_dec(v_startPos_1058_);
lean_dec_ref(v_str_1057_);
goto v___jp_1068_;
}
else
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_string_is_valid_pos(v_str_1057_, v_stopPos_1059_);
if (v___x_1072_ == 0)
{
lean_del_object(v___x_1061_);
lean_dec(v_stopPos_1059_);
lean_dec(v_startPos_1058_);
lean_dec_ref(v_str_1057_);
goto v___jp_1068_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_nat_dec_le(v_startPos_1058_, v_stopPos_1059_);
if (v___x_1073_ == 0)
{
lean_del_object(v___x_1061_);
lean_dec(v_stopPos_1059_);
lean_dec(v_startPos_1058_);
lean_dec_ref(v_str_1057_);
goto v___jp_1068_;
}
else
{
lean_object* v___x_1075_; 
if (v_isShared_1062_ == 0)
{
v___x_1075_ = v___x_1061_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_str_1057_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_startPos_1058_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_stopPos_1059_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
v___y_1065_ = v___x_1075_;
goto v___jp_1064_;
}
}
}
}
v___jp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_String_Slice_positions(v___y_1065_);
v___x_1067_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1065_, v___x_1066_, v___x_1063_);
lean_dec_ref(v___y_1065_);
return v___x_1067_;
}
v___jp_1068_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3);
v___x_1070_ = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(v___x_1069_);
v___y_1065_ = v___x_1070_;
goto v___jp_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object* v___y_1078_, lean_object* v_inst_1079_, lean_object* v_R_1080_, lean_object* v_a_1081_, lean_object* v_b_1082_, lean_object* v_c_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1078_, v_a_1081_, v_b_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object* v___y_1085_, lean_object* v_inst_1086_, lean_object* v_R_1087_, lean_object* v_a_1088_, lean_object* v_b_1089_, lean_object* v_c_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(v___y_1085_, v_inst_1086_, v_R_1087_, v_a_1088_, v_b_1089_, v_c_1090_);
lean_dec_ref(v___y_1085_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object* v_s_1092_, lean_object* v_stopPos_1093_, lean_object* v_i_1094_){
_start:
{
uint8_t v___y_1099_; uint8_t v___x_1100_; 
v___x_1100_ = lean_nat_dec_lt(v_i_1094_, v_stopPos_1093_);
if (v___x_1100_ == 0)
{
return v_i_1094_;
}
else
{
uint32_t v___x_1101_; uint8_t v___y_1103_; uint32_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1101_ = lean_string_utf8_get(v_s_1092_, v_i_1094_);
v___x_1108_ = 32;
v___x_1109_ = lean_uint32_dec_eq(v___x_1101_, v___x_1108_);
if (v___x_1109_ == 0)
{
uint32_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = 9;
v___x_1111_ = lean_uint32_dec_eq(v___x_1101_, v___x_1110_);
v___y_1103_ = v___x_1111_;
goto v___jp_1102_;
}
else
{
v___y_1103_ = v___x_1109_;
goto v___jp_1102_;
}
v___jp_1102_:
{
if (v___y_1103_ == 0)
{
uint32_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = 13;
v___x_1105_ = lean_uint32_dec_eq(v___x_1101_, v___x_1104_);
if (v___x_1105_ == 0)
{
uint32_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = 10;
v___x_1107_ = lean_uint32_dec_eq(v___x_1101_, v___x_1106_);
v___y_1099_ = v___x_1107_;
goto v___jp_1098_;
}
else
{
v___y_1099_ = v___x_1105_;
goto v___jp_1098_;
}
}
else
{
goto v___jp_1095_;
}
}
}
v___jp_1095_:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_string_utf8_next(v_s_1092_, v_i_1094_);
lean_dec(v_i_1094_);
v_i_1094_ = v___x_1096_;
goto _start;
}
v___jp_1098_:
{
if (v___y_1099_ == 0)
{
return v_i_1094_;
}
else
{
goto v___jp_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object* v_s_1112_, lean_object* v_stopPos_1113_, lean_object* v_i_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_s_1112_, v_stopPos_1113_, v_i_1114_);
lean_dec(v_stopPos_1113_);
lean_dec_ref(v_s_1112_);
return v_res_1115_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0));
v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2));
v___x_1121_ = l_Lean_stringToMessageData(v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object* v_lit_1122_, lean_object* v_i_1123_, lean_object* v_out_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v_escape_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; uint8_t v___x_1160_; 
v___x_1160_ = lean_string_utf8_at_end(v_lit_1122_, v_i_1123_);
if (v___x_1160_ == 0)
{
uint32_t v_curr_1161_; lean_object* v_i_1162_; uint32_t v___x_1163_; uint8_t v___x_1164_; 
v_curr_1161_ = lean_string_utf8_get_fast(v_lit_1122_, v_i_1123_);
v_i_1162_ = lean_string_utf8_next_fast(v_lit_1122_, v_i_1123_);
lean_dec(v_i_1123_);
v___x_1163_ = 92;
v___x_1164_ = lean_uint32_dec_eq(v_curr_1161_, v___x_1163_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_string_push(v_out_1124_, v_curr_1161_);
v_i_1123_ = v_i_1162_;
v_out_1124_ = v___x_1165_;
goto _start;
}
else
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_string_utf8_at_end(v_lit_1122_, v_i_1162_);
if (v___x_1167_ == 0)
{
uint32_t v_curr_1168_; lean_object* v_next_1169_; uint32_t v___x_1170_; uint8_t v___x_1171_; 
v_curr_1168_ = lean_string_utf8_get_fast(v_lit_1122_, v_i_1162_);
v_next_1169_ = lean_string_utf8_next_fast(v_lit_1122_, v_i_1162_);
v___x_1170_ = 98;
v___x_1171_ = lean_uint32_dec_eq(v_curr_1168_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 116;
v___x_1173_ = lean_uint32_dec_eq(v_curr_1168_, v___x_1172_);
if (v___x_1173_ == 0)
{
uint32_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = 110;
v___x_1175_ = lean_uint32_dec_eq(v_curr_1168_, v___x_1174_);
if (v___x_1175_ == 0)
{
uint32_t v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = 102;
v___x_1177_ = lean_uint32_dec_eq(v_curr_1168_, v___x_1176_);
if (v___x_1177_ == 0)
{
uint32_t v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = 114;
v___x_1179_ = lean_uint32_dec_eq(v_curr_1168_, v___x_1178_);
if (v___x_1179_ == 0)
{
uint32_t v___x_1180_; uint8_t v___x_1181_; 
v___x_1180_ = 34;
v___x_1181_ = lean_uint32_dec_eq(v_curr_1168_, v___x_1180_);
if (v___x_1181_ == 0)
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_uint32_dec_eq(v_curr_1168_, v___x_1163_);
if (v___x_1182_ == 0)
{
uint32_t v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = 117;
v___x_1184_ = lean_uint32_dec_eq(v_curr_1168_, v___x_1183_);
if (v___x_1184_ == 0)
{
uint32_t v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = 85;
v___x_1186_ = lean_uint32_dec_eq(v_curr_1168_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v_b_1188_; 
v___x_1187_ = lean_string_utf8_byte_size(v_lit_1122_);
v_b_1188_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_lit_1122_, v___x_1187_, v_i_1162_);
v_i_1123_ = v_b_1188_;
goto _start;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1190_ = lean_string_utf8_byte_size(v_lit_1122_);
lean_inc_ref_n(v_lit_1122_, 2);
v___x_1191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1191_, 0, v_lit_1122_);
lean_ctor_set(v___x_1191_, 1, v_next_1169_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
v___x_1192_ = lean_unsigned_to_nat(8u);
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = l_Substring_Raw_nextn(v___x_1191_, v___x_1192_, v___x_1193_);
lean_dec_ref(v___x_1191_);
v___x_1195_ = lean_nat_add(v_next_1169_, v___x_1194_);
lean_dec(v___x_1194_);
v___x_1196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1196_, 0, v_lit_1122_);
lean_ctor_set(v___x_1196_, 1, v_next_1169_);
lean_ctor_set(v___x_1196_, 2, v___x_1195_);
v_escape_1150_ = v___x_1196_;
v___y_1151_ = v_a_1125_;
v___y_1152_ = v_a_1126_;
goto v___jp_1149_;
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1197_ = lean_string_utf8_byte_size(v_lit_1122_);
lean_inc_ref_n(v_lit_1122_, 2);
v___x_1198_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1198_, 0, v_lit_1122_);
lean_ctor_set(v___x_1198_, 1, v_next_1169_);
lean_ctor_set(v___x_1198_, 2, v___x_1197_);
v___x_1199_ = lean_unsigned_to_nat(4u);
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = l_Substring_Raw_nextn(v___x_1198_, v___x_1199_, v___x_1200_);
lean_dec_ref(v___x_1198_);
v___x_1202_ = lean_nat_add(v_next_1169_, v___x_1201_);
lean_dec(v___x_1201_);
v___x_1203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1203_, 0, v_lit_1122_);
lean_ctor_set(v___x_1203_, 1, v_next_1169_);
lean_ctor_set(v___x_1203_, 2, v___x_1202_);
v_escape_1150_ = v___x_1203_;
v___y_1151_ = v_a_1125_;
v___y_1152_ = v_a_1126_;
goto v___jp_1149_;
}
}
else
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_string_push(v_out_1124_, v___x_1163_);
v_i_1123_ = v_next_1169_;
v_out_1124_ = v___x_1204_;
goto _start;
}
}
else
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_string_push(v_out_1124_, v___x_1180_);
v_i_1123_ = v_next_1169_;
v_out_1124_ = v___x_1206_;
goto _start;
}
}
else
{
uint32_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = 13;
v___x_1209_ = lean_string_push(v_out_1124_, v___x_1208_);
v_i_1123_ = v_next_1169_;
v_out_1124_ = v___x_1209_;
goto _start;
}
}
else
{
uint32_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = 12;
v___x_1212_ = lean_string_push(v_out_1124_, v___x_1211_);
v_i_1123_ = v_next_1169_;
v_out_1124_ = v___x_1212_;
goto _start;
}
}
else
{
uint32_t v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = 10;
v___x_1215_ = lean_string_push(v_out_1124_, v___x_1214_);
v_i_1123_ = v_next_1169_;
v_out_1124_ = v___x_1215_;
goto _start;
}
}
else
{
uint32_t v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = 9;
v___x_1218_ = lean_string_push(v_out_1124_, v___x_1217_);
v_i_1123_ = v_next_1169_;
v_out_1124_ = v___x_1218_;
goto _start;
}
}
else
{
uint32_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = 8;
v___x_1221_ = lean_string_push(v_out_1124_, v___x_1220_);
v_i_1123_ = v_next_1169_;
v_out_1124_ = v___x_1221_;
goto _start;
}
}
else
{
lean_object* v___x_1223_; 
lean_dec_ref(v_lit_1122_);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_out_1124_);
return v___x_1223_;
}
}
}
else
{
lean_object* v___x_1224_; 
lean_dec(v_i_1123_);
lean_dec_ref(v_lit_1122_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_out_1124_);
return v___x_1224_;
}
v___jp_1128_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1132_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1);
v___x_1133_ = lean_substring_tostring(v___y_1130_);
v___x_1134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
v___x_1135_ = l_Lean_MessageData_ofFormat(v___x_1134_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1132_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v___x_1138_, v___y_1129_, v___y_1131_);
return v___x_1139_;
}
v___jp_1140_:
{
lean_object* v_stopPos_1145_; uint32_t v_ch_1146_; lean_object* v___x_1147_; 
v_stopPos_1145_ = lean_ctor_get(v___y_1142_, 2);
lean_inc(v_stopPos_1145_);
lean_dec_ref(v___y_1142_);
v_ch_1146_ = lean_uint32_of_nat(v___y_1144_);
lean_dec(v___y_1144_);
v___x_1147_ = lean_string_push(v_out_1124_, v_ch_1146_);
v_i_1123_ = v_stopPos_1145_;
v_out_1124_ = v___x_1147_;
v_a_1125_ = v___y_1141_;
v_a_1126_ = v___y_1143_;
goto _start;
}
v___jp_1149_:
{
lean_object* v_val_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; 
lean_inc_ref(v_escape_1150_);
v_val_1153_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(v_escape_1150_);
v___x_1154_ = lean_unsigned_to_nat(55296u);
v___x_1155_ = lean_nat_dec_lt(v_val_1153_, v___x_1154_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1156_ = lean_unsigned_to_nat(57343u);
v___x_1157_ = lean_nat_dec_lt(v___x_1156_, v_val_1153_);
if (v___x_1157_ == 0)
{
lean_dec(v_val_1153_);
lean_dec_ref(v_out_1124_);
lean_dec_ref(v_lit_1122_);
v___y_1129_ = v___y_1151_;
v___y_1130_ = v_escape_1150_;
v___y_1131_ = v___y_1152_;
goto v___jp_1128_;
}
else
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = lean_unsigned_to_nat(1114112u);
v___x_1159_ = lean_nat_dec_lt(v_val_1153_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_dec(v_val_1153_);
lean_dec_ref(v_out_1124_);
lean_dec_ref(v_lit_1122_);
v___y_1129_ = v___y_1151_;
v___y_1130_ = v_escape_1150_;
v___y_1131_ = v___y_1152_;
goto v___jp_1128_;
}
else
{
v___y_1141_ = v___y_1151_;
v___y_1142_ = v_escape_1150_;
v___y_1143_ = v___y_1152_;
v___y_1144_ = v_val_1153_;
goto v___jp_1140_;
}
}
}
else
{
v___y_1141_ = v___y_1151_;
v___y_1142_ = v_escape_1150_;
v___y_1143_ = v___y_1152_;
v___y_1144_ = v_val_1153_;
goto v___jp_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object* v_lit_1225_, lean_object* v_i_1226_, lean_object* v_out_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v_lit_1225_, v_i_1226_, v_out_1227_, v_a_1228_, v_a_1229_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
return v_res_1231_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4));
v___x_1242_ = l_Lean_MessageData_ofFormat(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object* v_x_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_a_1248_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
v___x_1280_ = l_Lean_Syntax_isLit_x3f(v___x_1279_, v_x_1243_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_val_1281_; 
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref(v___x_1280_);
v_a_1248_ = v_val_1281_;
goto v___jp_1247_;
}
else
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec(v___x_1280_);
v___x_1282_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5);
v___x_1283_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1243_, v___x_1282_, v_a_1244_, v_a_1245_);
return v___x_1283_;
}
v___jp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_fileName_1252_; lean_object* v_fileMap_1253_; lean_object* v_options_1254_; lean_object* v_currRecDepth_1255_; lean_object* v_maxRecDepth_1256_; lean_object* v_ref_1257_; lean_object* v_currNamespace_1258_; lean_object* v_openDecls_1259_; lean_object* v_initHeartbeats_1260_; lean_object* v_maxHeartbeats_1261_; lean_object* v_quotContext_1262_; lean_object* v_currMacroScope_1263_; uint8_t v_diag_1264_; lean_object* v_cancelTk_x3f_1265_; uint8_t v_suppressElabErrors_1266_; lean_object* v_inheritedTraceOptions_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_ref_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_string_utf8_byte_size(v_a_1248_);
lean_inc_ref_n(v_a_1248_, 2);
v___x_1251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1251_, 0, v_a_1248_);
lean_ctor_set(v___x_1251_, 1, v___x_1249_);
lean_ctor_set(v___x_1251_, 2, v___x_1250_);
v_fileName_1252_ = lean_ctor_get(v_a_1244_, 0);
v_fileMap_1253_ = lean_ctor_get(v_a_1244_, 1);
v_options_1254_ = lean_ctor_get(v_a_1244_, 2);
v_currRecDepth_1255_ = lean_ctor_get(v_a_1244_, 3);
v_maxRecDepth_1256_ = lean_ctor_get(v_a_1244_, 4);
v_ref_1257_ = lean_ctor_get(v_a_1244_, 5);
v_currNamespace_1258_ = lean_ctor_get(v_a_1244_, 6);
v_openDecls_1259_ = lean_ctor_get(v_a_1244_, 7);
v_initHeartbeats_1260_ = lean_ctor_get(v_a_1244_, 8);
v_maxHeartbeats_1261_ = lean_ctor_get(v_a_1244_, 9);
v_quotContext_1262_ = lean_ctor_get(v_a_1244_, 10);
v_currMacroScope_1263_ = lean_ctor_get(v_a_1244_, 11);
v_diag_1264_ = lean_ctor_get_uint8(v_a_1244_, sizeof(void*)*14);
v_cancelTk_x3f_1265_ = lean_ctor_get(v_a_1244_, 12);
v_suppressElabErrors_1266_ = lean_ctor_get_uint8(v_a_1244_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1267_ = lean_ctor_get(v_a_1244_, 13);
v___x_1268_ = lean_unsigned_to_nat(1u);
v___x_1269_ = l_String_Slice_Pos_nextn(v___x_1251_, v___x_1249_, v___x_1268_);
lean_dec_ref(v___x_1251_);
lean_inc(v___x_1269_);
v___x_1270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1270_, 0, v_a_1248_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
lean_ctor_set(v___x_1270_, 2, v___x_1250_);
v___x_1271_ = lean_nat_sub(v___x_1250_, v___x_1269_);
v___x_1272_ = l_String_Slice_Pos_prevn(v___x_1270_, v___x_1271_, v___x_1268_);
lean_dec_ref(v___x_1270_);
v___x_1273_ = lean_nat_add(v___x_1269_, v___x_1272_);
lean_dec(v___x_1272_);
v___x_1274_ = lean_string_utf8_extract(v_a_1248_, v___x_1269_, v___x_1273_);
lean_dec(v___x_1273_);
lean_dec(v___x_1269_);
lean_dec_ref(v_a_1248_);
v___x_1275_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1276_ = l_Lean_replaceRef(v_x_1243_, v_ref_1257_);
lean_inc_ref(v_inheritedTraceOptions_1267_);
lean_inc(v_cancelTk_x3f_1265_);
lean_inc(v_currMacroScope_1263_);
lean_inc(v_quotContext_1262_);
lean_inc(v_maxHeartbeats_1261_);
lean_inc(v_initHeartbeats_1260_);
lean_inc(v_openDecls_1259_);
lean_inc(v_currNamespace_1258_);
lean_inc(v_maxRecDepth_1256_);
lean_inc(v_currRecDepth_1255_);
lean_inc_ref(v_options_1254_);
lean_inc_ref(v_fileMap_1253_);
lean_inc_ref(v_fileName_1252_);
v___x_1277_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1277_, 0, v_fileName_1252_);
lean_ctor_set(v___x_1277_, 1, v_fileMap_1253_);
lean_ctor_set(v___x_1277_, 2, v_options_1254_);
lean_ctor_set(v___x_1277_, 3, v_currRecDepth_1255_);
lean_ctor_set(v___x_1277_, 4, v_maxRecDepth_1256_);
lean_ctor_set(v___x_1277_, 5, v_ref_1276_);
lean_ctor_set(v___x_1277_, 6, v_currNamespace_1258_);
lean_ctor_set(v___x_1277_, 7, v_openDecls_1259_);
lean_ctor_set(v___x_1277_, 8, v_initHeartbeats_1260_);
lean_ctor_set(v___x_1277_, 9, v_maxHeartbeats_1261_);
lean_ctor_set(v___x_1277_, 10, v_quotContext_1262_);
lean_ctor_set(v___x_1277_, 11, v_currMacroScope_1263_);
lean_ctor_set(v___x_1277_, 12, v_cancelTk_x3f_1265_);
lean_ctor_set(v___x_1277_, 13, v_inheritedTraceOptions_1267_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14, v_diag_1264_);
lean_ctor_set_uint8(v___x_1277_, sizeof(void*)*14 + 1, v_suppressElabErrors_1266_);
v___x_1278_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1274_, v___x_1249_, v___x_1275_, v___x_1277_, v_a_1245_);
lean_dec_ref(v___x_1277_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object* v_x_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_x_1284_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object* v_s_1289_){
_start:
{
uint32_t v___y_1291_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_string_utf8_byte_size(v_s_1289_);
lean_inc_ref(v_s_1289_);
v___x_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1310_, 0, v_s_1289_);
lean_ctor_set(v___x_1310_, 1, v___x_1308_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
v___x_1311_ = l_String_Slice_Pos_get_x3f(v___x_1310_, v___x_1308_);
lean_dec_ref(v___x_1310_);
if (lean_obj_tag(v___x_1311_) == 0)
{
uint32_t v___x_1312_; 
v___x_1312_ = 65;
v___y_1291_ = v___x_1312_;
goto v___jp_1290_;
}
else
{
lean_object* v_val_1313_; uint32_t v___x_1314_; 
v_val_1313_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_val_1313_);
lean_dec_ref(v___x_1311_);
v___x_1314_ = lean_unbox_uint32(v_val_1313_);
lean_dec(v_val_1313_);
v___y_1291_ = v___x_1314_;
goto v___jp_1290_;
}
v___jp_1290_:
{
uint32_t v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = 13;
v___x_1293_ = lean_uint32_dec_eq(v___y_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
uint32_t v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = 10;
v___x_1295_ = lean_uint32_dec_eq(v___y_1291_, v___x_1294_);
if (v___x_1295_ == 0)
{
return v_s_1289_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_string_utf8_byte_size(v_s_1289_);
lean_inc_ref(v_s_1289_);
v___x_1299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1299_, 0, v_s_1289_);
lean_ctor_set(v___x_1299_, 1, v___x_1297_);
lean_ctor_set(v___x_1299_, 2, v___x_1298_);
v___x_1300_ = l_String_Slice_Pos_nextn(v___x_1299_, v___x_1297_, v___x_1296_);
lean_dec_ref(v___x_1299_);
v___x_1301_ = lean_string_utf8_extract(v_s_1289_, v___x_1300_, v___x_1298_);
lean_dec(v___x_1300_);
lean_dec_ref(v_s_1289_);
return v___x_1301_;
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1302_ = lean_unsigned_to_nat(2u);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_string_utf8_byte_size(v_s_1289_);
lean_inc_ref(v_s_1289_);
v___x_1305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1305_, 0, v_s_1289_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
lean_ctor_set(v___x_1305_, 2, v___x_1304_);
v___x_1306_ = l_String_Slice_Pos_nextn(v___x_1305_, v___x_1303_, v___x_1302_);
lean_dec_ref(v___x_1305_);
v___x_1307_ = lean_string_utf8_extract(v_s_1289_, v___x_1306_, v___x_1304_);
lean_dec(v___x_1306_);
lean_dec_ref(v_s_1289_);
return v___x_1307_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3));
v___x_1324_ = l_Lean_MessageData_ofFormat(v___x_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object* v_x_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_a_1330_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
v___x_1344_ = l_Lean_Syntax_isLit_x3f(v___x_1343_, v_x_1325_);
if (lean_obj_tag(v___x_1344_) == 1)
{
lean_object* v_val_1345_; 
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1345_);
lean_dec_ref(v___x_1344_);
v_a_1330_ = v_val_1345_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec(v___x_1344_);
v___x_1346_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4);
v___x_1347_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1325_, v___x_1346_, v_a_1326_, v_a_1327_);
return v___x_1347_;
}
v___jp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1331_ = lean_unsigned_to_nat(3u);
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = lean_string_utf8_byte_size(v_a_1330_);
lean_inc_ref_n(v_a_1330_, 2);
v___x_1334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1334_, 0, v_a_1330_);
lean_ctor_set(v___x_1334_, 1, v___x_1332_);
lean_ctor_set(v___x_1334_, 2, v___x_1333_);
v___x_1335_ = l_String_Slice_Pos_nextn(v___x_1334_, v___x_1332_, v___x_1331_);
lean_dec_ref(v___x_1334_);
lean_inc(v___x_1335_);
v___x_1336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1336_, 0, v_a_1330_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
lean_ctor_set(v___x_1336_, 2, v___x_1333_);
v___x_1337_ = lean_nat_sub(v___x_1333_, v___x_1335_);
v___x_1338_ = l_String_Slice_Pos_prevn(v___x_1336_, v___x_1337_, v___x_1331_);
lean_dec_ref(v___x_1336_);
v___x_1339_ = lean_nat_add(v___x_1335_, v___x_1338_);
lean_dec(v___x_1338_);
v___x_1340_ = lean_string_utf8_extract(v_a_1330_, v___x_1335_, v___x_1339_);
lean_dec(v___x_1339_);
lean_dec(v___x_1335_);
lean_dec_ref(v_a_1330_);
v___x_1341_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1340_);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object* v_x_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1348_, v_a_1349_, v_a_1350_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_x_1348_);
return v_res_1352_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4(void){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3));
v___x_1362_ = l_Lean_MessageData_ofFormat(v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object* v_x_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_a_1368_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
v___x_1401_ = l_Lean_Syntax_isLit_x3f(v___x_1400_, v_x_1363_);
if (lean_obj_tag(v___x_1401_) == 1)
{
lean_object* v_val_1402_; 
v_val_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_val_1402_);
lean_dec_ref(v___x_1401_);
v_a_1368_ = v_val_1402_;
goto v___jp_1367_;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v___x_1401_);
v___x_1403_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4);
v___x_1404_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1363_, v___x_1403_, v_a_1364_, v_a_1365_);
return v___x_1404_;
}
v___jp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_fileName_1372_; lean_object* v_fileMap_1373_; lean_object* v_options_1374_; lean_object* v_currRecDepth_1375_; lean_object* v_maxRecDepth_1376_; lean_object* v_ref_1377_; lean_object* v_currNamespace_1378_; lean_object* v_openDecls_1379_; lean_object* v_initHeartbeats_1380_; lean_object* v_maxHeartbeats_1381_; lean_object* v_quotContext_1382_; lean_object* v_currMacroScope_1383_; uint8_t v_diag_1384_; lean_object* v_cancelTk_x3f_1385_; uint8_t v_suppressElabErrors_1386_; lean_object* v_inheritedTraceOptions_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_ref_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___x_1370_ = lean_string_utf8_byte_size(v_a_1368_);
lean_inc_ref_n(v_a_1368_, 2);
v___x_1371_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1371_, 0, v_a_1368_);
lean_ctor_set(v___x_1371_, 1, v___x_1369_);
lean_ctor_set(v___x_1371_, 2, v___x_1370_);
v_fileName_1372_ = lean_ctor_get(v_a_1364_, 0);
v_fileMap_1373_ = lean_ctor_get(v_a_1364_, 1);
v_options_1374_ = lean_ctor_get(v_a_1364_, 2);
v_currRecDepth_1375_ = lean_ctor_get(v_a_1364_, 3);
v_maxRecDepth_1376_ = lean_ctor_get(v_a_1364_, 4);
v_ref_1377_ = lean_ctor_get(v_a_1364_, 5);
v_currNamespace_1378_ = lean_ctor_get(v_a_1364_, 6);
v_openDecls_1379_ = lean_ctor_get(v_a_1364_, 7);
v_initHeartbeats_1380_ = lean_ctor_get(v_a_1364_, 8);
v_maxHeartbeats_1381_ = lean_ctor_get(v_a_1364_, 9);
v_quotContext_1382_ = lean_ctor_get(v_a_1364_, 10);
v_currMacroScope_1383_ = lean_ctor_get(v_a_1364_, 11);
v_diag_1384_ = lean_ctor_get_uint8(v_a_1364_, sizeof(void*)*14);
v_cancelTk_x3f_1385_ = lean_ctor_get(v_a_1364_, 12);
v_suppressElabErrors_1386_ = lean_ctor_get_uint8(v_a_1364_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1387_ = lean_ctor_get(v_a_1364_, 13);
v___x_1388_ = lean_unsigned_to_nat(3u);
v___x_1389_ = l_String_Slice_Pos_nextn(v___x_1371_, v___x_1369_, v___x_1388_);
lean_dec_ref(v___x_1371_);
lean_inc(v___x_1389_);
v___x_1390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1390_, 0, v_a_1368_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
lean_ctor_set(v___x_1390_, 2, v___x_1370_);
v___x_1391_ = lean_nat_sub(v___x_1370_, v___x_1389_);
v___x_1392_ = l_String_Slice_Pos_prevn(v___x_1390_, v___x_1391_, v___x_1388_);
lean_dec_ref(v___x_1390_);
v___x_1393_ = lean_nat_add(v___x_1389_, v___x_1392_);
lean_dec(v___x_1392_);
v___x_1394_ = lean_string_utf8_extract(v_a_1368_, v___x_1389_, v___x_1393_);
lean_dec(v___x_1393_);
lean_dec(v___x_1389_);
lean_dec_ref(v_a_1368_);
v___x_1395_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1394_);
v___x_1396_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1397_ = l_Lean_replaceRef(v_x_1363_, v_ref_1377_);
lean_inc_ref(v_inheritedTraceOptions_1387_);
lean_inc(v_cancelTk_x3f_1385_);
lean_inc(v_currMacroScope_1383_);
lean_inc(v_quotContext_1382_);
lean_inc(v_maxHeartbeats_1381_);
lean_inc(v_initHeartbeats_1380_);
lean_inc(v_openDecls_1379_);
lean_inc(v_currNamespace_1378_);
lean_inc(v_maxRecDepth_1376_);
lean_inc(v_currRecDepth_1375_);
lean_inc_ref(v_options_1374_);
lean_inc_ref(v_fileMap_1373_);
lean_inc_ref(v_fileName_1372_);
v___x_1398_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1398_, 0, v_fileName_1372_);
lean_ctor_set(v___x_1398_, 1, v_fileMap_1373_);
lean_ctor_set(v___x_1398_, 2, v_options_1374_);
lean_ctor_set(v___x_1398_, 3, v_currRecDepth_1375_);
lean_ctor_set(v___x_1398_, 4, v_maxRecDepth_1376_);
lean_ctor_set(v___x_1398_, 5, v_ref_1397_);
lean_ctor_set(v___x_1398_, 6, v_currNamespace_1378_);
lean_ctor_set(v___x_1398_, 7, v_openDecls_1379_);
lean_ctor_set(v___x_1398_, 8, v_initHeartbeats_1380_);
lean_ctor_set(v___x_1398_, 9, v_maxHeartbeats_1381_);
lean_ctor_set(v___x_1398_, 10, v_quotContext_1382_);
lean_ctor_set(v___x_1398_, 11, v_currMacroScope_1383_);
lean_ctor_set(v___x_1398_, 12, v_cancelTk_x3f_1385_);
lean_ctor_set(v___x_1398_, 13, v_inheritedTraceOptions_1387_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*14, v_diag_1384_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*14 + 1, v_suppressElabErrors_1386_);
v___x_1399_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1395_, v___x_1369_, v___x_1396_, v___x_1398_, v_a_1365_);
lean_dec_ref(v___x_1398_);
return v___x_1399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object* v_x_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_x_1405_);
return v_res_1409_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2));
v___x_1417_ = l_Lean_stringToMessageData(v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object* v_x_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_){
_start:
{
lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_1418_);
v___x_1423_ = l_Lean_Syntax_isOfKind(v_x_1418_, v___x_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1425_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1418_, v___x_1424_, v_a_1419_, v_a_1420_);
lean_dec(v_x_1418_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; lean_object* v_x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1426_ = lean_unsigned_to_nat(0u);
v_x_1427_ = l_Lean_Syntax_getArg(v_x_1418_, v___x_1426_);
v___x_1428_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1427_);
v___x_1429_ = l_Lean_Syntax_isOfKind(v_x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1427_);
v___x_1431_ = l_Lean_Syntax_isOfKind(v_x_1427_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
lean_inc(v_x_1427_);
v___x_1433_ = l_Lean_Syntax_isOfKind(v_x_1427_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
lean_inc(v_x_1427_);
v___x_1435_ = l_Lean_Syntax_isOfKind(v_x_1427_, v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_x_1427_);
v___x_1436_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1437_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1418_, v___x_1436_, v_a_1419_, v_a_1420_);
lean_dec(v_x_1418_);
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; 
lean_dec(v_x_1418_);
v___x_1438_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1427_, v_a_1419_, v_a_1420_);
lean_dec(v_x_1427_);
return v___x_1438_;
}
}
else
{
lean_object* v___x_1439_; 
lean_dec(v_x_1418_);
v___x_1439_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1427_, v_a_1419_, v_a_1420_);
lean_dec(v_x_1427_);
return v___x_1439_;
}
}
else
{
lean_object* v___x_1440_; 
lean_dec(v_x_1418_);
v___x_1440_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1427_, v_a_1419_, v_a_1420_);
lean_dec(v_x_1427_);
return v___x_1440_;
}
}
else
{
lean_object* v___x_1441_; 
lean_dec(v_x_1418_);
v___x_1441_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1427_, v_a_1419_, v_a_1420_);
lean_dec(v_x_1427_);
return v___x_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object* v_x_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
return v_res_1446_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4(void){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3));
v___x_1456_ = l_Lean_MessageData_ofFormat(v___x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object* v_x_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1461_; lean_object* v_toApplicative_1462_; lean_object* v_toFunctor_1463_; lean_object* v_toSeq_1464_; lean_object* v_toSeqLeft_1465_; lean_object* v_toSeqRight_1466_; lean_object* v___x_1467_; lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___f_1470_; lean_object* v___f_1471_; lean_object* v___x_1472_; lean_object* v___f_1473_; lean_object* v___f_1474_; lean_object* v___f_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1461_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_1462_ = lean_ctor_get(v___x_1461_, 0);
v_toFunctor_1463_ = lean_ctor_get(v_toApplicative_1462_, 0);
v_toSeq_1464_ = lean_ctor_get(v_toApplicative_1462_, 2);
v_toSeqLeft_1465_ = lean_ctor_get(v_toApplicative_1462_, 3);
v_toSeqRight_1466_ = lean_ctor_get(v_toApplicative_1462_, 4);
v___x_1467_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
v___f_1468_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_1469_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref_n(v_toFunctor_1463_, 2);
v___f_1470_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1470_, 0, v_toFunctor_1463_);
v___f_1471_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1471_, 0, v_toFunctor_1463_);
v___x_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___f_1470_);
lean_ctor_set(v___x_1472_, 1, v___f_1471_);
lean_inc(v_toSeqRight_1466_);
v___f_1473_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1473_, 0, v_toSeqRight_1466_);
lean_inc(v_toSeqLeft_1465_);
v___f_1474_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1474_, 0, v_toSeqLeft_1465_);
lean_inc(v_toSeq_1464_);
v___f_1475_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1475_, 0, v_toSeq_1464_);
v___x_1476_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1472_);
lean_ctor_set(v___x_1476_, 1, v___f_1468_);
lean_ctor_set(v___x_1476_, 2, v___f_1475_);
lean_ctor_set(v___x_1476_, 3, v___f_1474_);
lean_ctor_set(v___x_1476_, 4, v___f_1473_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v___f_1469_);
v___x_1478_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_1479_ = l_Lean_Core_instMonadRefCoreM;
v___x_1480_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_1477_);
v___x_1481_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1480_, v___x_1477_);
v___x_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1478_);
lean_ctor_set(v___x_1482_, 1, v___x_1479_);
lean_ctor_set(v___x_1482_, 2, v___x_1481_);
v___x_1483_ = l_Lean_Syntax_isLit_x3f(v___x_1467_, v_x_1457_);
if (lean_obj_tag(v___x_1483_) == 1)
{
lean_object* v_val_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v___x_1482_);
lean_dec_ref(v___x_1477_);
lean_dec(v_x_1457_);
v_val_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_val_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set_tag(v___x_1486_, 0);
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_val_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
else
{
lean_object* v___x_1492_; lean_object* v___x_25__overap_1493_; lean_object* v___x_1494_; 
lean_dec(v___x_1483_);
v___x_1492_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_25__overap_1493_ = l_Lean_throwErrorAt___redArg(v___x_1477_, v___x_1482_, v_x_1457_, v___x_1492_);
lean_inc(v_a_1459_);
lean_inc_ref(v_a_1458_);
v___x_1494_ = lean_apply_3(v___x_25__overap_1493_, v_a_1458_, v_a_1459_, lean_box(0));
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object* v_x_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(v_x_1495_, v_a_1496_, v_a_1497_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
return v_res_1499_;
}
}
static lean_object* _init_l_Lake_Toml_elabSimpleKey___closed__3(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__2));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object* v_x_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1512_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__1));
lean_inc(v_x_1508_);
v___x_1513_ = l_Lean_Syntax_isOfKind(v_x_1508_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1515_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1508_, v___x_1514_, v_a_1509_, v_a_1510_);
lean_dec(v_x_1508_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; lean_object* v_x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v___x_1516_ = lean_unsigned_to_nat(0u);
v_x_1517_ = l_Lean_Syntax_getArg(v_x_1508_, v___x_1516_);
v___x_1518_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
lean_inc(v_x_1517_);
v___x_1519_ = l_Lean_Syntax_isOfKind(v_x_1517_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1520_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1517_);
v___x_1521_ = l_Lean_Syntax_isOfKind(v_x_1517_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1517_);
v___x_1523_ = l_Lean_Syntax_isOfKind(v_x_1517_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v_x_1517_);
v___x_1524_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1525_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1508_, v___x_1524_, v_a_1509_, v_a_1510_);
lean_dec(v_x_1508_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; 
lean_dec(v_x_1508_);
v___x_1526_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1517_, v_a_1509_, v_a_1510_);
lean_dec(v_x_1517_);
return v___x_1526_;
}
}
else
{
lean_object* v___x_1527_; 
lean_dec(v_x_1508_);
v___x_1527_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1517_, v_a_1509_, v_a_1510_);
lean_dec(v_x_1517_);
return v___x_1527_;
}
}
else
{
lean_object* v___x_1528_; 
lean_dec(v_x_1508_);
v___x_1528_ = l_Lean_Syntax_isLit_x3f(v___x_1518_, v_x_1517_);
if (lean_obj_tag(v___x_1528_) == 1)
{
lean_object* v_val_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_x_1517_);
v_val_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_val_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 0);
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_val_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v___x_1528_);
v___x_1537_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_1538_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1517_, v___x_1537_, v_a_1509_, v_a_1510_);
lean_dec(v_x_1517_);
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object* v_x_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lake_Toml_elabSimpleKey(v_x_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object* v_elabVal_1544_, size_t v_sz_1545_, size_t v_i_1546_, lean_object* v_bs_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_usize_dec_lt(v_i_1546_, v_sz_1545_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec_ref(v_elabVal_1544_);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_bs_1547_);
return v___x_1552_;
}
else
{
lean_object* v_v_1553_; lean_object* v___x_1554_; 
v_v_1553_ = lean_array_uget_borrowed(v_bs_1547_, v_i_1546_);
lean_inc_ref(v_elabVal_1544_);
lean_inc(v___y_1549_);
lean_inc_ref(v___y_1548_);
lean_inc(v_v_1553_);
v___x_1554_ = lean_apply_4(v_elabVal_1544_, v_v_1553_, v___y_1548_, v___y_1549_, lean_box(0));
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v_bs_x27_1557_; size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v___x_1556_ = lean_unsigned_to_nat(0u);
v_bs_x27_1557_ = lean_array_uset(v_bs_1547_, v_i_1546_, v___x_1556_);
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_add(v_i_1546_, v___x_1558_);
v___x_1560_ = lean_array_uset(v_bs_x27_1557_, v_i_1546_, v_a_1555_);
v_i_1546_ = v___x_1559_;
v_bs_1547_ = v___x_1560_;
goto _start;
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref(v_bs_1547_);
lean_dec_ref(v_elabVal_1544_);
v_a_1562_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1554_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1554_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object* v_elabVal_1570_, lean_object* v_sz_1571_, lean_object* v_i_1572_, lean_object* v_bs_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
size_t v_sz_boxed_1577_; size_t v_i_boxed_1578_; lean_object* v_res_1579_; 
v_sz_boxed_1577_ = lean_unbox_usize(v_sz_1571_);
lean_dec(v_sz_1571_);
v_i_boxed_1578_ = lean_unbox_usize(v_i_1572_);
lean_dec(v_i_1572_);
v_res_1579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1570_, v_sz_boxed_1577_, v_i_boxed_1578_, v_bs_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1579_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2));
v___x_1587_ = l_Lean_stringToMessageData(v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object* v_x_1588_, lean_object* v_elabVal_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_1588_);
v___x_1594_ = l_Lean_Syntax_isOfKind(v_x_1588_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec_ref(v_elabVal_1589_);
v___x_1595_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3);
v___x_1596_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1588_, v___x_1595_, v_a_1590_, v_a_1591_);
lean_dec(v_x_1588_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v_xs_1599_; lean_object* v___x_1600_; size_t v_sz_1601_; size_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1597_ = lean_unsigned_to_nat(1u);
v___x_1598_ = l_Lean_Syntax_getArg(v_x_1588_, v___x_1597_);
lean_dec(v_x_1588_);
v_xs_1599_ = l_Lean_Syntax_getArgs(v___x_1598_);
lean_dec(v___x_1598_);
v___x_1600_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1599_);
lean_dec_ref(v_xs_1599_);
v_sz_1601_ = lean_array_size(v___x_1600_);
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1589_, v_sz_1601_, v___x_1602_, v___x_1600_, v_a_1590_, v_a_1591_);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object* v_x_1604_, lean_object* v_elabVal_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1604_, v_elabVal_1605_, v_a_1606_, v_a_1607_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object* v_00_u03b1_1610_, lean_object* v_x_1611_, lean_object* v_elabVal_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1611_, v_elabVal_1612_, v_a_1613_, v_a_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object* v_00_u03b1_1617_, lean_object* v_x_1618_, lean_object* v_elabVal_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(v_00_u03b1_1617_, v_x_1618_, v_elabVal_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object* v_00_u03b1_1624_, lean_object* v_elabVal_1625_, size_t v_sz_1626_, size_t v_i_1627_, lean_object* v_bs_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1625_, v_sz_1626_, v_i_1627_, v_bs_1628_, v___y_1629_, v___y_1630_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object* v_00_u03b1_1633_, lean_object* v_elabVal_1634_, lean_object* v_sz_1635_, lean_object* v_i_1636_, lean_object* v_bs_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
size_t v_sz_boxed_1641_; size_t v_i_boxed_1642_; lean_object* v_res_1643_; 
v_sz_boxed_1641_ = lean_unbox_usize(v_sz_1635_);
lean_dec(v_sz_1635_);
v_i_boxed_1642_ = lean_unbox_usize(v_i_1636_);
lean_dec(v_i_1636_);
v_res_1643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(v_00_u03b1_1633_, v_elabVal_1634_, v_sz_boxed_1641_, v_i_boxed_1642_, v_bs_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(lean_object* v_msg_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v_ref_1648_; lean_object* v___x_1649_; lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1658_; 
v_ref_1648_ = lean_ctor_get(v___y_1645_, 5);
v___x_1649_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_1644_, v___y_1645_, v___y_1646_);
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1658_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
lean_inc(v_ref_1648_);
v___x_1654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1654_, 0, v_ref_1648_);
lean_ctor_set(v___x_1654_, 1, v_a_1650_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 1);
lean_ctor_set(v___x_1652_, 0, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg___boxed(lean_object* v_msg_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(lean_object* v_ref_1664_, lean_object* v_msg_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_fileName_1670_; lean_object* v_fileMap_1671_; lean_object* v_options_1672_; lean_object* v_currRecDepth_1673_; lean_object* v_maxRecDepth_1674_; lean_object* v_ref_1675_; lean_object* v_currNamespace_1676_; lean_object* v_openDecls_1677_; lean_object* v_initHeartbeats_1678_; lean_object* v_maxHeartbeats_1679_; lean_object* v_quotContext_1680_; lean_object* v_currMacroScope_1681_; uint8_t v_diag_1682_; lean_object* v_cancelTk_x3f_1683_; uint8_t v_suppressElabErrors_1684_; lean_object* v_inheritedTraceOptions_1685_; lean_object* v_ref_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_fileName_1670_ = lean_ctor_get(v___y_1667_, 0);
v_fileMap_1671_ = lean_ctor_get(v___y_1667_, 1);
v_options_1672_ = lean_ctor_get(v___y_1667_, 2);
v_currRecDepth_1673_ = lean_ctor_get(v___y_1667_, 3);
v_maxRecDepth_1674_ = lean_ctor_get(v___y_1667_, 4);
v_ref_1675_ = lean_ctor_get(v___y_1667_, 5);
v_currNamespace_1676_ = lean_ctor_get(v___y_1667_, 6);
v_openDecls_1677_ = lean_ctor_get(v___y_1667_, 7);
v_initHeartbeats_1678_ = lean_ctor_get(v___y_1667_, 8);
v_maxHeartbeats_1679_ = lean_ctor_get(v___y_1667_, 9);
v_quotContext_1680_ = lean_ctor_get(v___y_1667_, 10);
v_currMacroScope_1681_ = lean_ctor_get(v___y_1667_, 11);
v_diag_1682_ = lean_ctor_get_uint8(v___y_1667_, sizeof(void*)*14);
v_cancelTk_x3f_1683_ = lean_ctor_get(v___y_1667_, 12);
v_suppressElabErrors_1684_ = lean_ctor_get_uint8(v___y_1667_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1685_ = lean_ctor_get(v___y_1667_, 13);
v_ref_1686_ = l_Lean_replaceRef(v_ref_1664_, v_ref_1675_);
lean_inc_ref(v_inheritedTraceOptions_1685_);
lean_inc(v_cancelTk_x3f_1683_);
lean_inc(v_currMacroScope_1681_);
lean_inc(v_quotContext_1680_);
lean_inc(v_maxHeartbeats_1679_);
lean_inc(v_initHeartbeats_1678_);
lean_inc(v_openDecls_1677_);
lean_inc(v_currNamespace_1676_);
lean_inc(v_maxRecDepth_1674_);
lean_inc(v_currRecDepth_1673_);
lean_inc_ref(v_options_1672_);
lean_inc_ref(v_fileMap_1671_);
lean_inc_ref(v_fileName_1670_);
v___x_1687_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1687_, 0, v_fileName_1670_);
lean_ctor_set(v___x_1687_, 1, v_fileMap_1671_);
lean_ctor_set(v___x_1687_, 2, v_options_1672_);
lean_ctor_set(v___x_1687_, 3, v_currRecDepth_1673_);
lean_ctor_set(v___x_1687_, 4, v_maxRecDepth_1674_);
lean_ctor_set(v___x_1687_, 5, v_ref_1686_);
lean_ctor_set(v___x_1687_, 6, v_currNamespace_1676_);
lean_ctor_set(v___x_1687_, 7, v_openDecls_1677_);
lean_ctor_set(v___x_1687_, 8, v_initHeartbeats_1678_);
lean_ctor_set(v___x_1687_, 9, v_maxHeartbeats_1679_);
lean_ctor_set(v___x_1687_, 10, v_quotContext_1680_);
lean_ctor_set(v___x_1687_, 11, v_currMacroScope_1681_);
lean_ctor_set(v___x_1687_, 12, v_cancelTk_x3f_1683_);
lean_ctor_set(v___x_1687_, 13, v_inheritedTraceOptions_1685_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*14, v_diag_1682_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*14 + 1, v_suppressElabErrors_1684_);
v___x_1688_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_1665_, v___x_1687_, v___y_1668_);
lean_dec_ref(v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg___boxed(lean_object* v_ref_1689_, lean_object* v_msg_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v_ref_1689_, v_msg_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v_ref_1689_);
return v_res_1695_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object* v_t_1700_, uint8_t v___x_1701_, lean_object* v_as_1702_, size_t v_i_1703_, size_t v_stop_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_fst_1711_; lean_object* v_snd_1712_; uint8_t v___x_1716_; 
v___x_1716_ = lean_usize_dec_eq(v_i_1703_, v_stop_1704_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_array_uget_borrowed(v_as_1702_, v_i_1703_);
lean_inc(v___x_1717_);
v___x_1718_ = l_Lake_Toml_elabSimpleKey(v___x_1717_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1739_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1721_ = l_Lean_Name_str___override(v_b_1705_, v_a_1719_);
lean_inc_ref(v_t_1700_);
lean_inc(v___x_1721_);
v___x_1739_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1720_, v___x_1721_, v_t_1700_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_box(0);
lean_inc(v___x_1721_);
v___x_1741_ = l_Lake_Toml_RBDict_push___redArg(v___x_1720_, v___x_1721_, v___x_1740_, v___y_1706_);
v_fst_1711_ = v___x_1721_;
v_snd_1712_ = v___x_1741_;
goto v___jp_1710_;
}
else
{
lean_object* v_val_1742_; lean_object* v_snd_1743_; 
v_val_1742_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_val_1742_);
lean_dec_ref(v___x_1739_);
v_snd_1743_ = lean_ctor_get(v_val_1742_, 1);
lean_inc(v_snd_1743_);
lean_dec(v_val_1742_);
if (lean_obj_tag(v_snd_1743_) == 0)
{
if (v___x_1701_ == 0)
{
goto v___jp_1722_;
}
else
{
v_fst_1711_ = v___x_1721_;
v_snd_1712_ = v___y_1706_;
goto v___jp_1710_;
}
}
else
{
lean_dec_ref(v_snd_1743_);
goto v___jp_1722_;
}
}
v___jp_1722_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1723_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
lean_inc(v___x_1721_);
v___x_1724_ = l_Lean_MessageData_ofName(v___x_1721_);
v___x_1725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1723_);
lean_ctor_set(v___x_1725_, 1, v___x_1724_);
v___x_1726_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1725_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v___x_1717_, v___x_1727_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec_ref(v___y_1706_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v_snd_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
v_snd_1730_ = lean_ctor_get(v_a_1729_, 1);
lean_inc(v_snd_1730_);
lean_dec(v_a_1729_);
v_fst_1711_ = v___x_1721_;
v_snd_1712_ = v_snd_1730_;
goto v___jp_1710_;
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v___x_1721_);
lean_dec_ref(v_t_1700_);
v_a_1731_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1728_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1728_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec_ref(v___y_1706_);
lean_dec(v_b_1705_);
lean_dec_ref(v_t_1700_);
v_a_1744_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1718_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1718_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref(v_t_1700_);
v___x_1752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1752_, 0, v_b_1705_);
lean_ctor_set(v___x_1752_, 1, v___y_1706_);
v___x_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
return v___x_1753_;
}
v___jp_1710_:
{
size_t v___x_1713_; size_t v___x_1714_; 
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1703_, v___x_1713_);
v_i_1703_ = v___x_1714_;
v_b_1705_ = v_fst_1711_;
v___y_1706_ = v_snd_1712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object* v_t_1754_, lean_object* v___x_1755_, lean_object* v_as_1756_, lean_object* v_i_1757_, lean_object* v_stop_1758_, lean_object* v_b_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v___x_9533__boxed_1764_; size_t v_i_boxed_1765_; size_t v_stop_boxed_1766_; lean_object* v_res_1767_; 
v___x_9533__boxed_1764_ = lean_unbox(v___x_1755_);
v_i_boxed_1765_ = lean_unbox_usize(v_i_1757_);
lean_dec(v_i_1757_);
v_stop_boxed_1766_ = lean_unbox_usize(v_stop_1758_);
lean_dec(v_stop_1758_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_t_1754_, v___x_9533__boxed_1764_, v_as_1756_, v_i_boxed_1765_, v_stop_boxed_1766_, v_b_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec_ref(v_as_1756_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(size_t v_sz_1768_, size_t v_i_1769_, lean_object* v_bs_1770_){
_start:
{
uint8_t v___x_1771_; 
v___x_1771_ = lean_usize_dec_lt(v_i_1769_, v_sz_1768_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1772_, 0, v_bs_1770_);
return v___x_1772_;
}
else
{
lean_object* v_v_1773_; lean_object* v___x_1774_; lean_object* v_bs_x27_1775_; size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v_v_1773_ = lean_array_uget(v_bs_1770_, v_i_1769_);
v___x_1774_ = lean_unsigned_to_nat(0u);
v_bs_x27_1775_ = lean_array_uset(v_bs_1770_, v_i_1769_, v___x_1774_);
v___x_1776_ = ((size_t)1ULL);
v___x_1777_ = lean_usize_add(v_i_1769_, v___x_1776_);
v___x_1778_ = lean_array_uset(v_bs_x27_1775_, v_i_1769_, v_v_1773_);
v_i_1769_ = v___x_1777_;
v_bs_1770_ = v___x_1778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object* v_sz_1780_, lean_object* v_i_1781_, lean_object* v_bs_1782_){
_start:
{
size_t v_sz_boxed_1783_; size_t v_i_boxed_1784_; lean_object* v_res_1785_; 
v_sz_boxed_1783_ = lean_unbox_usize(v_sz_1780_);
lean_dec(v_sz_1780_);
v_i_boxed_1784_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_sz_boxed_1783_, v_i_boxed_1784_, v_bs_1782_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t v___x_1786_, lean_object* v_as_1787_, size_t v_i_1788_, size_t v_stop_1789_, lean_object* v_b_1790_){
_start:
{
lean_object* v___y_1792_; uint8_t v___x_1796_; 
v___x_1796_ = lean_usize_dec_eq(v_i_1788_, v_stop_1789_);
if (v___x_1796_ == 0)
{
lean_object* v_fst_1797_; uint8_t v___x_1798_; 
v_fst_1797_ = lean_ctor_get(v_b_1790_, 0);
v___x_1798_ = lean_unbox(v_fst_1797_);
if (v___x_1798_ == 0)
{
lean_object* v_snd_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1807_; 
v_snd_1799_ = lean_ctor_get(v_b_1790_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_b_1790_);
if (v_isSharedCheck_1807_ == 0)
{
lean_object* v_unused_1808_; 
v_unused_1808_ = lean_ctor_get(v_b_1790_, 0);
lean_dec(v_unused_1808_);
v___x_1801_ = v_b_1790_;
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snd_1799_);
lean_dec(v_b_1790_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = lean_box(v___x_1786_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1803_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_snd_1799_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
v___y_1792_ = v___x_1805_;
goto v___jp_1791_;
}
}
}
else
{
lean_object* v_snd_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1819_; 
v_snd_1809_ = lean_ctor_get(v_b_1790_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_b_1790_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v_b_1790_, 0);
lean_dec(v_unused_1820_);
v___x_1811_ = v_b_1790_;
v_isShared_1812_ = v_isSharedCheck_1819_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_snd_1809_);
lean_dec(v_b_1790_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1819_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1813_ = lean_array_uget_borrowed(v_as_1787_, v_i_1788_);
lean_inc(v___x_1813_);
v___x_1814_ = lean_array_push(v_snd_1809_, v___x_1813_);
v___x_1815_ = lean_box(v___x_1796_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 1, v___x_1814_);
lean_ctor_set(v___x_1811_, 0, v___x_1815_);
v___x_1817_ = v___x_1811_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1814_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
v___y_1792_ = v___x_1817_;
goto v___jp_1791_;
}
}
}
}
else
{
return v_b_1790_;
}
v___jp_1791_:
{
size_t v___x_1793_; size_t v___x_1794_; 
v___x_1793_ = ((size_t)1ULL);
v___x_1794_ = lean_usize_add(v_i_1788_, v___x_1793_);
v_i_1788_ = v___x_1794_;
v_b_1790_ = v___y_1792_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object* v___x_1821_, lean_object* v_as_1822_, lean_object* v_i_1823_, lean_object* v_stop_1824_, lean_object* v_b_1825_){
_start:
{
uint8_t v___x_9654__boxed_1826_; size_t v_i_boxed_1827_; size_t v_stop_boxed_1828_; lean_object* v_res_1829_; 
v___x_9654__boxed_1826_ = lean_unbox(v___x_1821_);
v_i_boxed_1827_ = lean_unbox_usize(v_i_1823_);
lean_dec(v_i_1823_);
v_stop_boxed_1828_ = lean_unbox_usize(v_stop_1824_);
lean_dec(v_stop_1824_);
v_res_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_9654__boxed_1826_, v_as_1822_, v_i_boxed_1827_, v_stop_boxed_1828_, v_b_1825_);
lean_dec_ref(v_as_1822_);
return v_res_1829_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object* v_elabVal_1848_, lean_object* v_as_1849_, size_t v_i_1850_, size_t v_stop_1851_, lean_object* v_b_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_a_1857_; lean_object* v___y_1862_; uint8_t v___x_1864_; 
v___x_1864_ = lean_usize_dec_eq(v_i_1850_, v_stop_1851_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1));
v___x_1866_ = lean_array_uget_borrowed(v_as_1849_, v_i_1850_);
lean_inc(v___x_1866_);
v___x_1867_ = l_Lean_Syntax_isOfKind(v___x_1866_, v___x_1865_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref(v_b_1852_);
v___x_1868_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3);
v___x_1869_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1866_, v___x_1868_, v___y_1853_, v___y_1854_);
v___y_1862_ = v___x_1869_;
goto v___jp_1861_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1870_ = lean_unsigned_to_nat(0u);
v___x_1871_ = l_Lean_Syntax_getArg(v___x_1866_, v___x_1870_);
v___x_1872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5));
lean_inc(v___x_1871_);
v___x_1873_ = l_Lean_Syntax_isOfKind(v___x_1871_, v___x_1872_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref(v_b_1852_);
v___x_1874_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1875_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1871_, v___x_1874_, v___y_1853_, v___y_1854_);
lean_dec(v___x_1871_);
v___y_1862_ = v___x_1875_;
goto v___jp_1861_;
}
else
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_v_1878_; lean_object* v___y_1880_; lean_object* v_fst_1881_; lean_object* v_snd_1882_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1928_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1876_ = lean_unsigned_to_nat(2u);
v___x_1877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v_v_1878_ = l_Lean_Syntax_getArg(v___x_1866_, v___x_1876_);
v___x_1949_ = l_Lean_Syntax_getArg(v___x_1871_, v___x_1870_);
v___x_1950_ = l_Lean_Syntax_getArgs(v___x_1949_);
lean_dec(v___x_1949_);
v___x_1951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8));
v___x_1952_ = lean_array_get_size(v___x_1950_);
v___x_1953_ = lean_nat_dec_lt(v___x_1870_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_dec_ref(v___x_1950_);
v___y_1928_ = v___x_1951_;
goto v___jp_1927_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1954_ = lean_box(v___x_1873_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v___x_1951_);
v___x_1956_ = lean_nat_dec_le(v___x_1952_, v___x_1952_);
if (v___x_1956_ == 0)
{
if (v___x_1953_ == 0)
{
lean_dec_ref(v___x_1955_);
lean_dec_ref(v___x_1950_);
v___y_1928_ = v___x_1951_;
goto v___jp_1927_;
}
else
{
size_t v___x_1957_; size_t v___x_1958_; lean_object* v___x_1959_; lean_object* v_snd_1960_; 
v___x_1957_ = ((size_t)0ULL);
v___x_1958_ = lean_usize_of_nat(v___x_1952_);
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1873_, v___x_1950_, v___x_1957_, v___x_1958_, v___x_1955_);
lean_dec_ref(v___x_1950_);
v_snd_1960_ = lean_ctor_get(v___x_1959_, 1);
lean_inc(v_snd_1960_);
lean_dec_ref(v___x_1959_);
v___y_1928_ = v_snd_1960_;
goto v___jp_1927_;
}
}
else
{
size_t v___x_1961_; size_t v___x_1962_; lean_object* v___x_1963_; lean_object* v_snd_1964_; 
v___x_1961_ = ((size_t)0ULL);
v___x_1962_ = lean_usize_of_nat(v___x_1952_);
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1873_, v___x_1950_, v___x_1961_, v___x_1962_, v___x_1955_);
lean_dec_ref(v___x_1950_);
v_snd_1964_ = lean_ctor_get(v___x_1963_, 1);
lean_inc(v_snd_1964_);
lean_dec_ref(v___x_1963_);
v___y_1928_ = v_snd_1964_;
goto v___jp_1927_;
}
}
v___jp_1879_:
{
lean_object* v___x_1883_; 
lean_inc(v___y_1880_);
v___x_1883_ = l_Lake_Toml_elabSimpleKey(v___y_1880_, v___y_1853_, v___y_1854_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_Name_str___override(v_fst_1881_, v_a_1884_);
lean_inc_ref(v_snd_1882_);
lean_inc(v___x_1885_);
v___x_1886_ = l_Lake_Toml_RBDict_contains___redArg(v___x_1877_, v___x_1885_, v_snd_1882_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; 
lean_dec(v___y_1880_);
lean_inc_ref(v_elabVal_1848_);
lean_inc(v___y_1854_);
lean_inc_ref(v___y_1853_);
v___x_1887_ = lean_apply_4(v_elabVal_1848_, v_v_1878_, v___y_1853_, v___y_1854_, lean_box(0));
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
v___x_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1889_, 0, v_a_1888_);
v___x_1890_ = l_Lake_Toml_RBDict_push___redArg(v___x_1877_, v___x_1885_, v___x_1889_, v_snd_1882_);
v_a_1857_ = v___x_1890_;
goto v___jp_1856_;
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v___x_1885_);
lean_dec_ref(v_snd_1882_);
lean_dec_ref(v_elabVal_1848_);
v_a_1891_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1887_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1887_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_dec_ref(v_snd_1882_);
lean_dec(v_v_1878_);
v___x_1899_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
v___x_1900_ = l_Lean_MessageData_ofName(v___x_1885_);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___y_1880_, v___x_1903_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1880_);
v___y_1862_ = v___x_1904_;
goto v___jp_1861_;
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_snd_1882_);
lean_dec(v_fst_1881_);
lean_dec(v___y_1880_);
lean_dec(v_v_1878_);
lean_dec_ref(v_elabVal_1848_);
v_a_1905_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1883_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1883_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
v___jp_1913_:
{
if (lean_obj_tag(v___y_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v_fst_1917_; lean_object* v_snd_1918_; 
v_a_1916_ = lean_ctor_get(v___y_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___y_1915_);
v_fst_1917_ = lean_ctor_get(v_a_1916_, 0);
lean_inc(v_fst_1917_);
v_snd_1918_ = lean_ctor_get(v_a_1916_, 1);
lean_inc(v_snd_1918_);
lean_dec(v_a_1916_);
v___y_1880_ = v___y_1914_;
v_fst_1881_ = v_fst_1917_;
v_snd_1882_ = v_snd_1918_;
goto v___jp_1879_;
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v___y_1914_);
lean_dec(v_v_1878_);
lean_dec_ref(v_elabVal_1848_);
v_a_1919_ = lean_ctor_get(v___y_1915_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___y_1915_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___y_1915_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___y_1915_);
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
v___jp_1927_:
{
size_t v_sz_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v_sz_1929_ = lean_array_size(v___y_1928_);
v___x_1930_ = ((size_t)0ULL);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_sz_1929_, v___x_1930_, v___y_1928_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_dec(v_v_1878_);
lean_dec_ref(v_b_1852_);
v___x_1932_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1933_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1871_, v___x_1932_, v___y_1853_, v___y_1854_);
lean_dec(v___x_1871_);
v___y_1862_ = v___x_1933_;
goto v___jp_1861_;
}
else
{
lean_object* v_val_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v_tailKey_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
lean_dec(v___x_1871_);
v_val_1934_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_val_1934_);
lean_dec_ref(v___x_1931_);
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_array_get_size(v_val_1934_);
v___x_1937_ = lean_unsigned_to_nat(1u);
v___x_1938_ = lean_nat_sub(v___x_1936_, v___x_1937_);
v_tailKey_1939_ = lean_array_get(v___x_1935_, v_val_1934_, v___x_1938_);
lean_dec(v___x_1938_);
v___x_1940_ = lean_box(0);
v___x_1941_ = lean_array_pop(v_val_1934_);
v___x_1942_ = lean_array_get_size(v___x_1941_);
v___x_1943_ = lean_nat_dec_lt(v___x_1870_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_dec_ref(v___x_1941_);
v___y_1880_ = v_tailKey_1939_;
v_fst_1881_ = v___x_1940_;
v_snd_1882_ = v_b_1852_;
goto v___jp_1879_;
}
else
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_nat_dec_le(v___x_1942_, v___x_1942_);
if (v___x_1944_ == 0)
{
if (v___x_1943_ == 0)
{
lean_dec_ref(v___x_1941_);
v___y_1880_ = v_tailKey_1939_;
v_fst_1881_ = v___x_1940_;
v_snd_1882_ = v_b_1852_;
goto v___jp_1879_;
}
else
{
size_t v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_usize_of_nat(v___x_1942_);
lean_inc_ref(v_b_1852_);
v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1852_, v___x_1873_, v___x_1941_, v___x_1930_, v___x_1945_, v___x_1940_, v_b_1852_, v___y_1853_, v___y_1854_);
lean_dec_ref(v___x_1941_);
v___y_1914_ = v_tailKey_1939_;
v___y_1915_ = v___x_1946_;
goto v___jp_1913_;
}
}
else
{
size_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1947_ = lean_usize_of_nat(v___x_1942_);
lean_inc_ref(v_b_1852_);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1852_, v___x_1873_, v___x_1941_, v___x_1930_, v___x_1947_, v___x_1940_, v_b_1852_, v___y_1853_, v___y_1854_);
lean_dec_ref(v___x_1941_);
v___y_1914_ = v_tailKey_1939_;
v___y_1915_ = v___x_1948_;
goto v___jp_1913_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1965_; 
lean_dec_ref(v_elabVal_1848_);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_b_1852_);
return v___x_1965_;
}
v___jp_1856_:
{
size_t v___x_1858_; size_t v___x_1859_; 
v___x_1858_ = ((size_t)1ULL);
v___x_1859_ = lean_usize_add(v_i_1850_, v___x_1858_);
v_i_1850_ = v___x_1859_;
v_b_1852_ = v_a_1857_;
goto _start;
}
v___jp_1861_:
{
if (lean_obj_tag(v___y_1862_) == 0)
{
lean_object* v_a_1863_; 
v_a_1863_ = lean_ctor_get(v___y_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref(v___y_1862_);
v_a_1857_ = v_a_1863_;
goto v___jp_1856_;
}
else
{
lean_dec_ref(v_elabVal_1848_);
return v___y_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object* v_elabVal_1966_, lean_object* v_as_1967_, lean_object* v_i_1968_, lean_object* v_stop_1969_, lean_object* v_b_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
size_t v_i_boxed_1974_; size_t v_stop_boxed_1975_; lean_object* v_res_1976_; 
v_i_boxed_1974_ = lean_unbox_usize(v_i_1968_);
lean_dec(v_i_1968_);
v_stop_boxed_1975_ = lean_unbox_usize(v_stop_1969_);
lean_dec(v_stop_1969_);
v_res_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1966_, v_as_1967_, v_i_boxed_1974_, v_stop_boxed_1975_, v_b_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec_ref(v_as_1967_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object* v_as_1977_, size_t v_i_1978_, size_t v_stop_1979_, lean_object* v_b_1980_){
_start:
{
lean_object* v___y_1982_; uint8_t v___x_1986_; 
v___x_1986_ = lean_usize_dec_eq(v_i_1978_, v_stop_1979_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v_snd_1988_; 
v___x_1987_ = lean_array_uget_borrowed(v_as_1977_, v_i_1978_);
v_snd_1988_ = lean_ctor_get(v___x_1987_, 1);
if (lean_obj_tag(v_snd_1988_) == 1)
{
lean_object* v_fst_1989_; lean_object* v_val_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_fst_1989_ = lean_ctor_get(v___x_1987_, 0);
v_val_1990_ = lean_ctor_get(v_snd_1988_, 0);
v___x_1991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
lean_inc(v_val_1990_);
lean_inc(v_fst_1989_);
v___x_1992_ = l_Lake_Toml_RBDict_push___redArg(v___x_1991_, v_fst_1989_, v_val_1990_, v_b_1980_);
v___y_1982_ = v___x_1992_;
goto v___jp_1981_;
}
else
{
v___y_1982_ = v_b_1980_;
goto v___jp_1981_;
}
}
else
{
return v_b_1980_;
}
v___jp_1981_:
{
size_t v___x_1983_; size_t v___x_1984_; 
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1978_, v___x_1983_);
v_i_1978_ = v___x_1984_;
v_b_1980_ = v___y_1982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object* v_as_1993_, lean_object* v_i_1994_, lean_object* v_stop_1995_, lean_object* v_b_1996_){
_start:
{
size_t v_i_boxed_1997_; size_t v_stop_boxed_1998_; lean_object* v_res_1999_; 
v_i_boxed_1997_ = lean_unbox_usize(v_i_1994_);
lean_dec(v_i_1994_);
v_stop_boxed_1998_ = lean_unbox_usize(v_stop_1995_);
lean_dec(v_stop_1995_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_as_1993_, v_i_boxed_1997_, v_stop_boxed_1998_, v_b_1996_);
lean_dec_ref(v_as_1993_);
return v_res_1999_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2));
v___x_2007_ = l_Lean_stringToMessageData(v___x_2006_);
return v___x_2007_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_2009_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_2008_);
return v___x_2009_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5(void){
_start:
{
lean_object* v___x_2010_; lean_object* v_t_2011_; 
v___x_2010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v_t_2011_ = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), v___x_2010_);
return v_t_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object* v_x_2012_, lean_object* v_elabVal_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2012_);
v___x_2018_ = l_Lean_Syntax_isOfKind(v_x_2012_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
lean_dec_ref(v_elabVal_2013_);
v___x_2019_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3);
v___x_2020_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2012_, v___x_2019_, v_a_2014_, v_a_2015_);
lean_dec(v_x_2012_);
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v_kvs_2024_; lean_object* v_a_2026_; lean_object* v___y_2043_; lean_object* v_t_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2021_ = lean_unsigned_to_nat(0u);
v___x_2022_ = lean_unsigned_to_nat(1u);
v___x_2023_ = l_Lean_Syntax_getArg(v_x_2012_, v___x_2022_);
lean_dec(v_x_2012_);
v_kvs_2024_ = l_Lean_Syntax_getArgs(v___x_2023_);
lean_dec(v___x_2023_);
v_t_2053_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__5);
v___x_2054_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_kvs_2024_);
lean_dec_ref(v_kvs_2024_);
v___x_2055_ = lean_array_get_size(v___x_2054_);
v___x_2056_ = lean_nat_dec_lt(v___x_2021_, v___x_2055_);
if (v___x_2056_ == 0)
{
lean_dec_ref(v___x_2054_);
lean_dec_ref(v_elabVal_2013_);
v_a_2026_ = v_t_2053_;
goto v___jp_2025_;
}
else
{
uint8_t v___x_2057_; 
v___x_2057_ = lean_nat_dec_le(v___x_2055_, v___x_2055_);
if (v___x_2057_ == 0)
{
if (v___x_2056_ == 0)
{
lean_dec_ref(v___x_2054_);
lean_dec_ref(v_elabVal_2013_);
v_a_2026_ = v_t_2053_;
goto v___jp_2025_;
}
else
{
size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2058_ = ((size_t)0ULL);
v___x_2059_ = lean_usize_of_nat(v___x_2055_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_2013_, v___x_2054_, v___x_2058_, v___x_2059_, v_t_2053_, v_a_2014_, v_a_2015_);
lean_dec_ref(v___x_2054_);
v___y_2043_ = v___x_2060_;
goto v___jp_2042_;
}
}
else
{
size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = ((size_t)0ULL);
v___x_2062_ = lean_usize_of_nat(v___x_2055_);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_2013_, v___x_2054_, v___x_2061_, v___x_2062_, v_t_2053_, v_a_2014_, v_a_2015_);
lean_dec_ref(v___x_2054_);
v___y_2043_ = v___x_2063_;
goto v___jp_2042_;
}
}
v___jp_2025_:
{
lean_object* v_items_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v_items_2027_ = lean_ctor_get(v_a_2026_, 0);
lean_inc_ref(v_items_2027_);
lean_dec_ref(v_a_2026_);
v___x_2028_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
v___x_2029_ = lean_array_get_size(v_items_2027_);
v___x_2030_ = lean_nat_dec_lt(v___x_2021_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_dec_ref(v_items_2027_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2028_);
return v___x_2031_;
}
else
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_nat_dec_le(v___x_2029_, v___x_2029_);
if (v___x_2032_ == 0)
{
if (v___x_2030_ == 0)
{
lean_object* v___x_2033_; 
lean_dec_ref(v_items_2027_);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2028_);
return v___x_2033_;
}
else
{
size_t v___x_2034_; size_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2034_ = ((size_t)0ULL);
v___x_2035_ = lean_usize_of_nat(v___x_2029_);
v___x_2036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_2027_, v___x_2034_, v___x_2035_, v___x_2028_);
lean_dec_ref(v_items_2027_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
}
else
{
size_t v___x_2038_; size_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2038_ = ((size_t)0ULL);
v___x_2039_ = lean_usize_of_nat(v___x_2029_);
v___x_2040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_2027_, v___x_2038_, v___x_2039_, v___x_2028_);
lean_dec_ref(v_items_2027_);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
}
v___jp_2042_:
{
if (lean_obj_tag(v___y_2043_) == 0)
{
lean_object* v_a_2044_; 
v_a_2044_ = lean_ctor_get(v___y_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___y_2043_);
v_a_2026_ = v_a_2044_;
goto v___jp_2025_;
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
v_a_2045_ = lean_ctor_get(v___y_2043_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___y_2043_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___y_2043_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___y_2043_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object* v_x_2064_, lean_object* v_elabVal_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2064_, v_elabVal_2065_, v_a_2066_, v_a_2067_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(lean_object* v_00_u03b1_2070_, lean_object* v_ref_2071_, lean_object* v_msg_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___redArg(v_ref_2071_, v_msg_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object* v_00_u03b1_2078_, lean_object* v_ref_2079_, lean_object* v_msg_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_00_u03b1_2078_, v_ref_2079_, v_msg_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v_ref_2079_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(lean_object* v_00_u03b1_2086_, lean_object* v_msg_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___redArg(v_msg_2087_, v___y_2089_, v___y_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2093_, lean_object* v_msg_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1_spec__1(v_00_u03b1_2093_, v_msg_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2099_;
}
}
static lean_object* _init_l_Lake_Toml_elabVal___closed__1(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = ((lean_object*)(l_Lake_Toml_elabVal___closed__0));
v___x_2102_ = l_Lean_stringToMessageData(v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object* v_x_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lake_Toml_elabVal(v_x_2103_, v_a_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object* v_x_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
lean_inc(v_x_2108_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
lean_inc(v_x_2108_);
v___x_2115_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
lean_inc(v_x_2108_);
v___x_2117_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
lean_inc(v_x_2108_);
v___x_2119_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
lean_inc(v_x_2108_);
v___x_2121_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
lean_inc(v_x_2108_);
v___x_2123_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_2108_);
v___x_2125_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2126_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_2108_);
v___x_2127_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; uint8_t v___x_2129_; 
v___x_2128_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_2108_);
v___x_2129_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2128_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2108_);
v___x_2131_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_obj_once(&l_Lake_Toml_elabVal___closed__1, &l_Lake_Toml_elabVal___closed__1_once, _init_l_Lake_Toml_elabVal___closed__1);
v___x_2133_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2108_, v___x_2132_, v_a_2109_, v_a_2110_);
lean_dec(v_x_2108_);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2108_);
v___x_2135_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2108_, v___x_2134_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2144_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_x_2108_);
lean_ctor_set(v___x_2140_, 1, v_a_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_x_2108_);
v_a_2145_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2135_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2135_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2108_);
v___x_2154_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_2108_, v___x_2153_, v_a_2109_, v_a_2110_);
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
v___x_2159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2159_, 0, v_x_2108_);
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
lean_dec(v_x_2108_);
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
lean_inc(v_x_2108_);
v___x_2172_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_2108_, v_a_2109_, v_a_2110_);
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
lean_object* v___x_2177_; uint8_t v___x_2178_; lean_object* v___x_2180_; 
v___x_2177_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_2177_, 0, v_x_2108_);
v___x_2178_ = lean_unbox(v_a_2173_);
lean_dec(v_a_2173_);
lean_ctor_set_uint8(v___x_2177_, sizeof(void*)*1, v___x_2178_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2177_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2177_);
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
lean_dec(v_x_2108_);
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
lean_inc(v_x_2108_);
v___x_2191_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2200_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2196_, 0, v_x_2108_);
lean_ctor_set(v___x_2196_, 1, v_a_2192_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2196_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_x_2108_);
v_a_2201_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2191_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2191_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
else
{
lean_object* v___x_2209_; 
v___x_2209_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2218_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2218_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2218_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2214_, 0, v_x_2108_);
lean_ctor_set(v___x_2214_, 1, v_a_2210_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2214_);
v___x_2216_ = v___x_2212_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v_x_2108_);
v_a_2219_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2209_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2209_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
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
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2237_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2237_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2237_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2232_ = lean_nat_to_int(v_a_2228_);
v___x_2233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_x_2108_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2233_);
v___x_2235_ = v___x_2230_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_x_2108_);
v_a_2238_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2227_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2227_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
else
{
lean_object* v___x_2246_; 
v___x_2246_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2256_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2251_ = lean_nat_to_int(v_a_2247_);
v___x_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2252_, 0, v_x_2108_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2252_);
v___x_2254_ = v___x_2249_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_x_2108_);
v_a_2257_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2246_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2246_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2275_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2275_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2275_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2270_ = lean_nat_to_int(v_a_2266_);
v___x_2271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2271_, 0, v_x_2108_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2271_);
v___x_2273_ = v___x_2268_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_x_2108_);
v_a_2276_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2265_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2265_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_object* v___x_2284_; 
v___x_2284_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2293_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
v___x_2289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_x_2108_);
lean_ctor_set(v___x_2289_, 1, v_a_2285_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v___x_2289_);
v___x_2291_ = v___x_2287_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v_x_2108_);
v_a_2294_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2284_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2284_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
else
{
lean_object* v___x_2302_; 
v___x_2302_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_2108_, v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2312_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2312_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2312_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2307_; double v___x_2308_; lean_object* v___x_2310_; 
v___x_2307_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_2307_, 0, v_x_2108_);
v___x_2308_ = lean_unbox_float(v_a_2303_);
lean_dec(v_a_2303_);
lean_ctor_set_float(v___x_2307_, sizeof(void*)*1, v___x_2308_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2307_);
v___x_2310_ = v___x_2305_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2307_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_x_2108_);
v_a_2313_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2302_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2302_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
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
