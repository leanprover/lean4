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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lake_Toml_RBDict_empty___redArg();
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0;
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
v___x_1_ = l_instMonadEIO___redArg();
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
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_239__overap_50_; lean_object* v___x_51_; 
lean_dec(v___x_35_);
v___x_44_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4));
v___x_45_ = lean_string_append(v___x_44_, v_name_10_);
v___x_46_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5));
v___x_47_ = lean_string_append(v___x_45_, v___x_46_);
v___x_48_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
v___x_49_ = l_Lean_MessageData_ofFormat(v___x_48_);
v___x_239__overap_50_ = l_Lean_throwErrorAt___redArg(v___x_29_, v___x_34_, v_x_9_, v___x_49_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
v___x_51_ = lean_apply_3(v___x_239__overap_50_, v_a_11_, v_a_12_, lean_box(0));
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
v___x_59_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_string_utf8_byte_size(v_s_228_);
v___x_231_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_230_, v_s_228_, v___x_229_, v___x_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum___boxed(lean_object* v_s_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_s_232_);
lean_dec_ref(v_s_232_);
return v_res_233_;
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
lean_dec_ref(v_snd_286_);
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
lean_dec_ref(v___x_306_);
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
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_fst_399_; lean_object* v_snd_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_string_utf8_byte_size(v_s_394_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_396_, v_s_394_, v___x_395_, v___x_397_);
v_fst_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_fst_399_);
v_snd_400_ = lean_ctor_get(v___x_398_, 1);
lean_inc(v_snd_400_);
v___x_401_ = lean_string_length(v_s_394_);
v___x_402_ = lean_nat_dec_le(v___x_401_, v_snd_400_);
lean_dec(v_snd_400_);
if (v___x_402_ == 0)
{
lean_dec(v_fst_399_);
return v___x_398_;
}
else
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_410_ = lean_ctor_get(v___x_398_, 1);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v___x_398_, 0);
lean_dec(v_unused_411_);
v___x_404_ = v___x_398_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_dec(v___x_398_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_395_);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_fst_399_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_395_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa___boxed(lean_object* v_s_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_s_412_);
lean_dec_ref(v_s_412_);
return v_res_413_;
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg(){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___closed__0));
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___boxed(lean_object* v___dummy_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg();
return v_res_437_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0(void){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg();
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object* v_s_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object* v_s_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v_s_441_);
lean_dec_ref(v_s_441_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object* v_s_443_, lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_it_449_; lean_object* v_startInclusive_450_; lean_object* v_endExclusive_451_; 
if (lean_obj_tag(v_a_446_) == 0)
{
lean_object* v_currPos_456_; lean_object* v_searcher_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_484_; 
v_currPos_456_ = lean_ctor_get(v_a_446_, 0);
v_searcher_457_ = lean_ctor_get(v_a_446_, 1);
v_isSharedCheck_484_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_484_ == 0)
{
v___x_459_ = v_a_446_;
v_isShared_460_ = v_isSharedCheck_484_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_searcher_457_);
lean_inc(v_currPos_456_);
lean_dec(v_a_446_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_484_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
uint8_t v___y_462_; uint8_t v_decide_477_; 
v_decide_477_ = lean_nat_dec_eq(v_searcher_457_, v___x_445_);
if (v_decide_477_ == 0)
{
uint32_t v___x_478_; uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_478_ = lean_string_utf8_get_fast(v_s_443_, v_searcher_457_);
v___x_479_ = 69;
v___x_480_ = lean_uint32_dec_eq(v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 101;
v___x_482_ = lean_uint32_dec_eq(v___x_478_, v___x_481_);
v___y_462_ = v___x_482_;
goto v___jp_461_;
}
else
{
v___y_462_ = v___x_480_;
goto v___jp_461_;
}
}
else
{
lean_object* v___x_483_; 
lean_del_object(v___x_459_);
lean_dec(v_searcher_457_);
v___x_483_ = lean_box(1);
lean_inc(v___x_445_);
v_it_449_ = v___x_483_;
v_startInclusive_450_ = v_currPos_456_;
v_endExclusive_451_ = v___x_445_;
goto v___jp_448_;
}
v___jp_461_:
{
if (v___y_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_string_utf8_next_fast(v_s_443_, v_searcher_457_);
lean_dec(v_searcher_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_463_);
v___x_465_ = v___x_459_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_currPos_456_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_463_);
v___x_465_ = v_reuseFailAlloc_467_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
v_a_446_ = v___x_465_;
goto _start;
}
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v_slice_471_; lean_object* v_nextIt_473_; 
v___x_468_ = lean_string_utf8_next_fast(v_s_443_, v_searcher_457_);
v___x_469_ = lean_nat_sub(v___x_468_, v_searcher_457_);
v___x_470_ = lean_nat_add(v_searcher_457_, v___x_469_);
lean_dec(v___x_469_);
v_slice_471_ = l_String_Slice_subslice_x21(v___x_444_, v_currPos_456_, v_searcher_457_);
lean_inc(v___x_470_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_470_);
lean_ctor_set(v___x_459_, 0, v___x_470_);
v_nextIt_473_ = v___x_459_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_470_);
v_nextIt_473_ = v_reuseFailAlloc_476_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v_startInclusive_474_; lean_object* v_endExclusive_475_; 
v_startInclusive_474_ = lean_ctor_get(v_slice_471_, 0);
lean_inc(v_startInclusive_474_);
v_endExclusive_475_ = lean_ctor_get(v_slice_471_, 1);
lean_inc(v_endExclusive_475_);
lean_dec_ref(v_slice_471_);
v_it_449_ = v_nextIt_473_;
v_startInclusive_450_ = v_startInclusive_474_;
v_endExclusive_451_ = v_endExclusive_475_;
goto v___jp_448_;
}
}
}
}
}
else
{
lean_dec(v___x_445_);
lean_dec_ref(v_s_443_);
return v_b_447_;
}
v___jp_448_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_inc_ref(v_s_443_);
v___x_452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_452_, 0, v_s_443_);
lean_ctor_set(v___x_452_, 1, v_startInclusive_450_);
lean_ctor_set(v___x_452_, 2, v_endExclusive_451_);
v___x_453_ = l_String_Slice_toString(v___x_452_);
lean_dec_ref_known(v___x_452_, 3);
v___x_454_ = lean_array_push(v_b_447_, v___x_453_);
v_a_446_ = v_it_449_;
v_b_447_ = v___x_454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object* v_s_485_, lean_object* v___x_486_, lean_object* v___x_487_, lean_object* v_a_488_, lean_object* v_b_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_485_, v___x_486_, v___x_487_, v_a_488_, v_b_489_);
lean_dec_ref(v___x_486_);
return v_res_490_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_nat_to_int(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object* v_s_498_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lean_string_utf8_byte_size(v_s_498_);
lean_inc_ref(v_s_498_);
v___x_503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_503_, 0, v_s_498_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
lean_ctor_set(v___x_503_, 2, v___x_502_);
v___x_504_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0);
v___x_505_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2));
v___x_506_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_498_, v___x_503_, v___x_502_, v___x_504_, v___x_505_);
lean_dec_ref_known(v___x_503_, 3);
v___x_507_ = lean_array_to_list(v___x_506_);
if (lean_obj_tag(v___x_507_) == 1)
{
lean_object* v_tail_508_; 
v_tail_508_ = lean_ctor_get(v___x_507_, 1);
lean_inc(v_tail_508_);
if (lean_obj_tag(v_tail_508_) == 0)
{
lean_object* v_head_509_; lean_object* v___x_510_; lean_object* v_fst_511_; lean_object* v_snd_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_520_; 
v_head_509_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_head_509_);
lean_dec_ref_known(v___x_507_, 2);
v___x_510_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_509_);
lean_dec(v_head_509_);
v_fst_511_ = lean_ctor_get(v___x_510_, 0);
v_snd_512_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_520_ == 0)
{
v___x_514_ = v___x_510_;
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snd_512_);
lean_inc(v_fst_511_);
lean_dec(v___x_510_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_520_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = l_Int_negOfNat(v_snd_512_);
lean_dec(v_snd_512_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_fst_511_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v_tail_521_; 
v_tail_521_ = lean_ctor_get(v_tail_508_, 1);
if (lean_obj_tag(v_tail_521_) == 0)
{
lean_object* v_head_522_; lean_object* v_head_523_; lean_object* v___x_524_; lean_object* v_fst_525_; lean_object* v_snd_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_536_; 
v_head_522_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_head_522_);
lean_dec_ref_known(v___x_507_, 2);
v_head_523_ = lean_ctor_get(v_tail_508_, 0);
lean_inc(v_head_523_);
lean_dec_ref_known(v_tail_508_, 2);
v___x_524_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_522_);
lean_dec(v_head_522_);
v_fst_525_ = lean_ctor_get(v___x_524_, 0);
v_snd_526_ = lean_ctor_get(v___x_524_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_536_ == 0)
{
v___x_528_ = v___x_524_;
v_isShared_529_ = v_isSharedCheck_536_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_snd_526_);
lean_inc(v_fst_525_);
lean_dec(v___x_524_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_536_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_exp_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v_exp_530_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_head_523_);
v___x_531_ = l_Int_negOfNat(v_snd_526_);
lean_dec(v_snd_526_);
v___x_532_ = lean_int_add(v___x_531_, v_exp_530_);
lean_dec(v_exp_530_);
lean_dec(v___x_531_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 1, v___x_532_);
v___x_534_ = v___x_528_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_fst_525_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
else
{
lean_dec_ref_known(v_tail_508_, 2);
lean_dec_ref_known(v___x_507_, 2);
goto v___jp_499_;
}
}
}
else
{
lean_dec(v___x_507_);
goto v___jp_499_;
}
v___jp_499_:
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object* v_s_537_, lean_object* v___x_538_, lean_object* v___x_539_, lean_object* v_inst_540_, lean_object* v_R_541_, lean_object* v_a_542_, lean_object* v_b_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_537_, v___x_538_, v___x_539_, v_a_542_, v_b_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object* v_s_545_, lean_object* v___x_546_, lean_object* v___x_547_, lean_object* v_inst_548_, lean_object* v_R_549_, lean_object* v_a_550_, lean_object* v_b_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(v_s_545_, v___x_546_, v___x_547_, v_inst_548_, v_R_549_, v_a_550_, v_b_551_);
lean_dec_ref(v___x_546_);
return v_res_552_;
}
}
static double _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2(void){
_start:
{
lean_object* v___x_555_; double v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = lean_float_of_nat(v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object* v_s_557_){
_start:
{
lean_object* v___x_558_; lean_object* v_fst_559_; lean_object* v_snd_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_558_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(v_s_557_);
v_fst_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_fst_559_);
v_snd_560_ = lean_ctor_get(v___x_558_, 1);
lean_inc(v_snd_560_);
lean_dec_ref(v___x_558_);
v___x_561_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0));
v___x_562_ = lean_string_dec_eq(v_snd_560_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1));
v___x_564_ = lean_string_dec_eq(v_snd_560_, v___x_563_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v___x_568_; uint8_t v___x_569_; lean_object* v___x_570_; double v_flt_571_; uint8_t v___x_572_; 
v___x_565_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(v_snd_560_);
v_fst_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_fst_566_);
v_snd_567_ = lean_ctor_get(v___x_565_, 1);
lean_inc(v_snd_567_);
lean_dec_ref(v___x_565_);
v___x_568_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_569_ = lean_int_dec_lt(v_snd_567_, v___x_568_);
v___x_570_ = lean_nat_abs(v_snd_567_);
lean_dec(v_snd_567_);
v_flt_571_ = l_Float_ofScientific(v_fst_566_, v___x_569_, v___x_570_);
v___x_572_ = lean_unbox(v_fst_559_);
lean_dec(v_fst_559_);
if (v___x_572_ == 0)
{
return v_flt_571_;
}
else
{
double v___x_573_; 
v___x_573_ = lean_float_negate(v_flt_571_);
return v___x_573_;
}
}
else
{
uint8_t v___x_574_; 
lean_dec(v_snd_560_);
v___x_574_ = lean_unbox(v_fst_559_);
lean_dec(v_fst_559_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; double v___x_577_; double v___x_578_; double v___x_579_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = l_Float_ofScientific(v___x_575_, v___x_564_, v___x_576_);
v___x_578_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_579_ = lean_float_div(v___x_577_, v___x_578_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; double v___x_582_; double v___x_583_; double v___x_584_; double v___x_585_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = l_Float_ofScientific(v___x_580_, v___x_564_, v___x_581_);
v___x_583_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_584_ = lean_float_div(v___x_582_, v___x_583_);
v___x_585_ = lean_float_negate(v___x_584_);
return v___x_585_;
}
}
}
else
{
uint8_t v___x_586_; 
lean_dec(v_snd_560_);
v___x_586_ = lean_unbox(v_fst_559_);
lean_dec(v_fst_559_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; double v___x_589_; double v___x_590_; double v___x_591_; 
v___x_587_ = lean_unsigned_to_nat(10u);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = l_Float_ofScientific(v___x_587_, v___x_562_, v___x_588_);
v___x_590_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_591_ = lean_float_div(v___x_589_, v___x_590_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; double v___x_594_; double v___x_595_; double v___x_596_; double v___x_597_; 
v___x_592_ = lean_unsigned_to_nat(10u);
v___x_593_ = lean_unsigned_to_nat(1u);
v___x_594_ = l_Float_ofScientific(v___x_592_, v___x_562_, v___x_593_);
v___x_595_ = lean_float_negate(v___x_594_);
v___x_596_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_597_ = lean_float_div(v___x_595_, v___x_596_);
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object* v_s_598_){
_start:
{
double v_res_599_; lean_object* v_r_600_; 
v_res_599_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_s_598_);
v_r_600_ = lean_box_float(v_res_599_);
return v_r_600_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3));
v___x_610_ = l_Lean_MessageData_ofFormat(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object* v_x_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_a_616_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
v___x_621_ = l_Lean_Syntax_isLit_x3f(v___x_620_, v_x_611_);
if (lean_obj_tag(v___x_621_) == 1)
{
lean_object* v_val_622_; 
v_val_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_val_622_);
lean_dec_ref_known(v___x_621_, 1);
v_a_616_ = v_val_622_;
goto v___jp_615_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v___x_621_);
v___x_623_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4);
v___x_624_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_611_, v___x_623_, v_a_612_, v_a_613_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
v___jp_615_:
{
double v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_a_616_);
v___x_618_ = lean_box_float(v___x_617_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object* v_x_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_x_633_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object* v___x_638_, lean_object* v___x_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
lean_object* v___x_643_; uint8_t v_decide_644_; 
v___x_643_ = lean_nat_sub(v___x_638_, v___x_639_);
v_decide_644_ = lean_nat_dec_eq(v_a_641_, v___x_643_);
lean_dec(v___x_643_);
if (v_decide_644_ == 0)
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint32_t v___x_648_; uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_645_ = lean_nat_add(v___x_639_, v_a_641_);
lean_dec(v_a_641_);
v___x_646_ = lean_string_utf8_next_fast(v_a_640_, v___x_645_);
v___x_647_ = lean_nat_sub(v___x_646_, v___x_639_);
v___x_648_ = lean_string_utf8_get_fast(v_a_640_, v___x_645_);
lean_dec(v___x_645_);
v___x_649_ = 95;
v___x_650_ = lean_uint32_dec_eq(v___x_648_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; uint32_t v___x_653_; uint32_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = lean_unsigned_to_nat(2u);
v___x_652_ = lean_nat_mul(v_b_642_, v___x_651_);
lean_dec(v_b_642_);
v___x_653_ = 48;
v___x_654_ = lean_uint32_sub(v___x_648_, v___x_653_);
v___x_655_ = lean_uint32_to_nat(v___x_654_);
v___x_656_ = lean_nat_add(v___x_652_, v___x_655_);
lean_dec(v___x_655_);
lean_dec(v___x_652_);
v_a_641_ = v___x_647_;
v_b_642_ = v___x_656_;
goto _start;
}
else
{
v_a_641_ = v___x_647_;
goto _start;
}
}
else
{
lean_dec(v_a_641_);
return v_b_642_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object* v___x_659_, lean_object* v___x_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_b_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_659_, v___x_660_, v_a_661_, v_a_662_, v_b_663_);
lean_dec_ref(v_a_661_);
lean_dec(v___x_660_);
lean_dec(v___x_659_);
return v_res_664_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3));
v___x_674_ = l_Lean_MessageData_ofFormat(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object* v_x_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_a_680_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
v___x_689_ = l_Lean_Syntax_isLit_x3f(v___x_688_, v_x_675_);
if (lean_obj_tag(v___x_689_) == 1)
{
lean_object* v_val_690_; 
v_val_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___x_689_, 1);
v_a_680_ = v_val_690_;
goto v___jp_679_;
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec(v___x_689_);
v___x_691_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4);
v___x_692_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_675_, v___x_691_, v_a_676_, v_a_677_);
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_unsigned_to_nat(2u);
v___x_683_ = lean_string_utf8_byte_size(v_a_680_);
lean_inc_ref(v_a_680_);
v___x_684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_684_, 0, v_a_680_);
lean_ctor_set(v___x_684_, 1, v___x_681_);
lean_ctor_set(v___x_684_, 2, v___x_683_);
v___x_685_ = l_String_Slice_Pos_nextn(v___x_684_, v___x_681_, v___x_682_);
lean_dec_ref_known(v___x_684_, 3);
v___x_686_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_683_, v___x_685_, v_a_680_, v___x_681_, v___x_681_);
lean_dec_ref(v_a_680_);
lean_dec(v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object* v_x_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_701_, v_a_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_x_701_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object* v___x_706_, lean_object* v___x_707_, lean_object* v___x_708_, lean_object* v_a_709_, lean_object* v_inst_710_, lean_object* v_R_711_, lean_object* v_a_712_, lean_object* v_b_713_, lean_object* v_c_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_706_, v___x_707_, v_a_709_, v_a_712_, v_b_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v___x_718_, lean_object* v_a_719_, lean_object* v_inst_720_, lean_object* v_R_721_, lean_object* v_a_722_, lean_object* v_b_723_, lean_object* v_c_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(v___x_716_, v___x_717_, v___x_718_, v_a_719_, v_inst_720_, v_R_721_, v_a_722_, v_b_723_, v_c_724_);
lean_dec_ref(v_a_719_);
lean_dec_ref(v___x_718_);
lean_dec(v___x_717_);
lean_dec(v___x_716_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object* v___x_726_, lean_object* v___x_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_b_730_){
_start:
{
lean_object* v___x_731_; uint8_t v_decide_732_; 
v___x_731_ = lean_nat_sub(v___x_726_, v___x_727_);
v_decide_732_ = lean_nat_dec_eq(v_a_729_, v___x_731_);
lean_dec(v___x_731_);
if (v_decide_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint32_t v___x_736_; uint32_t v___x_737_; uint8_t v___x_738_; 
v___x_733_ = lean_nat_add(v___x_727_, v_a_729_);
lean_dec(v_a_729_);
v___x_734_ = lean_string_utf8_next_fast(v_a_728_, v___x_733_);
v___x_735_ = lean_nat_sub(v___x_734_, v___x_727_);
v___x_736_ = lean_string_utf8_get_fast(v_a_728_, v___x_733_);
lean_dec(v___x_733_);
v___x_737_ = 95;
v___x_738_ = lean_uint32_dec_eq(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; uint32_t v___x_741_; uint32_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_739_ = lean_unsigned_to_nat(8u);
v___x_740_ = lean_nat_mul(v_b_730_, v___x_739_);
lean_dec(v_b_730_);
v___x_741_ = 48;
v___x_742_ = lean_uint32_sub(v___x_736_, v___x_741_);
v___x_743_ = lean_uint32_to_nat(v___x_742_);
v___x_744_ = lean_nat_add(v___x_740_, v___x_743_);
lean_dec(v___x_743_);
lean_dec(v___x_740_);
v_a_729_ = v___x_735_;
v_b_730_ = v___x_744_;
goto _start;
}
else
{
v_a_729_ = v___x_735_;
goto _start;
}
}
else
{
lean_dec(v_a_729_);
return v_b_730_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object* v___x_747_, lean_object* v___x_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_b_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_747_, v___x_748_, v_a_749_, v_a_750_, v_b_751_);
lean_dec_ref(v_a_749_);
lean_dec(v___x_748_);
lean_dec(v___x_747_);
return v_res_752_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3));
v___x_762_ = l_Lean_MessageData_ofFormat(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object* v_x_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_a_768_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
v___x_777_ = l_Lean_Syntax_isLit_x3f(v___x_776_, v_x_763_);
if (lean_obj_tag(v___x_777_) == 1)
{
lean_object* v_val_778_; 
v_val_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_val_778_);
lean_dec_ref_known(v___x_777_, 1);
v_a_768_ = v_val_778_;
goto v___jp_767_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v___x_777_);
v___x_779_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4);
v___x_780_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_763_, v___x_779_, v_a_764_, v_a_765_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_780_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
v___jp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_unsigned_to_nat(2u);
v___x_771_ = lean_string_utf8_byte_size(v_a_768_);
lean_inc_ref(v_a_768_);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v_a_768_);
lean_ctor_set(v___x_772_, 1, v___x_769_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
v___x_773_ = l_String_Slice_Pos_nextn(v___x_772_, v___x_769_, v___x_770_);
lean_dec_ref_known(v___x_772_, 3);
v___x_774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_771_, v___x_773_, v_a_768_, v___x_769_, v___x_769_);
lean_dec_ref(v_a_768_);
lean_dec(v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object* v_x_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_789_, v_a_790_, v_a_791_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_x_789_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object* v___x_794_, lean_object* v___x_795_, lean_object* v___x_796_, lean_object* v_a_797_, lean_object* v_inst_798_, lean_object* v_R_799_, lean_object* v_a_800_, lean_object* v_b_801_, lean_object* v_c_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_794_, v___x_795_, v_a_797_, v_a_800_, v_b_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object* v___x_804_, lean_object* v___x_805_, lean_object* v___x_806_, lean_object* v_a_807_, lean_object* v_inst_808_, lean_object* v_R_809_, lean_object* v_a_810_, lean_object* v_b_811_, lean_object* v_c_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(v___x_804_, v___x_805_, v___x_806_, v_a_807_, v_inst_808_, v_R_809_, v_a_810_, v_b_811_, v_c_812_);
lean_dec_ref(v_a_807_);
lean_dec_ref(v___x_806_);
lean_dec(v___x_805_);
lean_dec(v___x_804_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t v_c_814_){
_start:
{
uint32_t v___x_815_; uint8_t v___x_816_; 
v___x_815_ = 57;
v___x_816_ = lean_uint32_dec_le(v_c_814_, v___x_815_);
if (v___x_816_ == 0)
{
uint32_t v___x_817_; uint8_t v___x_818_; 
v___x_817_ = 70;
v___x_818_ = lean_uint32_dec_le(v_c_814_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; uint32_t v___x_820_; uint32_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_819_ = lean_unsigned_to_nat(10u);
v___x_820_ = 97;
v___x_821_ = lean_uint32_sub(v_c_814_, v___x_820_);
v___x_822_ = lean_uint32_to_nat(v___x_821_);
v___x_823_ = lean_nat_add(v___x_819_, v___x_822_);
lean_dec(v___x_822_);
return v___x_823_;
}
else
{
lean_object* v___x_824_; uint32_t v___x_825_; uint32_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_824_ = lean_unsigned_to_nat(10u);
v___x_825_ = 65;
v___x_826_ = lean_uint32_sub(v_c_814_, v___x_825_);
v___x_827_ = lean_uint32_to_nat(v___x_826_);
v___x_828_ = lean_nat_add(v___x_824_, v___x_827_);
lean_dec(v___x_827_);
return v___x_828_;
}
}
else
{
uint32_t v___x_829_; uint32_t v___x_830_; lean_object* v___x_831_; 
v___x_829_ = 48;
v___x_830_ = lean_uint32_sub(v_c_814_, v___x_829_);
v___x_831_ = lean_uint32_to_nat(v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object* v_c_832_){
_start:
{
uint32_t v_c_boxed_833_; lean_object* v_res_834_; 
v_c_boxed_833_ = lean_unbox_uint32(v_c_832_);
lean_dec(v_c_832_);
v_res_834_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v_c_boxed_833_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object* v___x_835_, lean_object* v___x_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_b_839_){
_start:
{
lean_object* v___x_840_; uint8_t v_decide_841_; 
v___x_840_ = lean_nat_sub(v___x_835_, v___x_836_);
v_decide_841_ = lean_nat_dec_eq(v_a_838_, v___x_840_);
lean_dec(v___x_840_);
if (v_decide_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; uint32_t v___x_845_; uint32_t v___x_846_; uint8_t v___x_847_; 
v___x_842_ = lean_nat_add(v___x_836_, v_a_838_);
lean_dec(v_a_838_);
v___x_843_ = lean_string_utf8_next_fast(v_a_837_, v___x_842_);
v___x_844_ = lean_nat_sub(v___x_843_, v___x_836_);
v___x_845_ = lean_string_utf8_get_fast(v_a_837_, v___x_842_);
lean_dec(v___x_842_);
v___x_846_ = 95;
v___x_847_ = lean_uint32_dec_eq(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_848_ = lean_unsigned_to_nat(16u);
v___x_849_ = lean_nat_mul(v_b_839_, v___x_848_);
lean_dec(v_b_839_);
v___x_850_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_845_);
v___x_851_ = lean_nat_add(v___x_849_, v___x_850_);
lean_dec(v___x_850_);
lean_dec(v___x_849_);
v_a_838_ = v___x_844_;
v_b_839_ = v___x_851_;
goto _start;
}
else
{
v_a_838_ = v___x_844_;
goto _start;
}
}
else
{
lean_dec(v_a_838_);
return v_b_839_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object* v___x_854_, lean_object* v___x_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_b_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_854_, v___x_855_, v_a_856_, v_a_857_, v_b_858_);
lean_dec_ref(v_a_856_);
lean_dec(v___x_855_);
lean_dec(v___x_854_);
return v_res_859_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3));
v___x_869_ = l_Lean_MessageData_ofFormat(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object* v_x_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_a_875_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
v___x_884_ = l_Lean_Syntax_isLit_x3f(v___x_883_, v_x_870_);
if (lean_obj_tag(v___x_884_) == 1)
{
lean_object* v_val_885_; 
v_val_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_val_885_);
lean_dec_ref_known(v___x_884_, 1);
v_a_875_ = v_val_885_;
goto v___jp_874_;
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v___x_884_);
v___x_886_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4);
v___x_887_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_870_, v___x_886_, v_a_871_, v_a_872_);
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
v___jp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = lean_unsigned_to_nat(2u);
v___x_878_ = lean_string_utf8_byte_size(v_a_875_);
lean_inc_ref(v_a_875_);
v___x_879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_879_, 0, v_a_875_);
lean_ctor_set(v___x_879_, 1, v___x_876_);
lean_ctor_set(v___x_879_, 2, v___x_878_);
v___x_880_ = l_String_Slice_Pos_nextn(v___x_879_, v___x_876_, v___x_877_);
lean_dec_ref_known(v___x_879_, 3);
v___x_881_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_878_, v___x_880_, v_a_875_, v___x_876_, v___x_876_);
lean_dec_ref(v_a_875_);
lean_dec(v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object* v_x_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_896_, v_a_897_, v_a_898_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_x_896_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v_a_904_, lean_object* v_inst_905_, lean_object* v_R_906_, lean_object* v_a_907_, lean_object* v_b_908_, lean_object* v_c_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_901_, v___x_902_, v_a_904_, v_a_907_, v_b_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v_a_914_, lean_object* v_inst_915_, lean_object* v_R_916_, lean_object* v_a_917_, lean_object* v_b_918_, lean_object* v_c_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(v___x_911_, v___x_912_, v___x_913_, v_a_914_, v_inst_915_, v_R_916_, v_a_917_, v_b_918_, v_c_919_);
lean_dec_ref(v_a_914_);
lean_dec_ref(v___x_913_);
lean_dec(v___x_912_);
lean_dec(v___x_911_);
return v_res_920_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5));
v___x_933_ = l_Lean_MessageData_ofFormat(v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object* v_x_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_a_939_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
v___x_952_ = l_Lean_Syntax_isLit_x3f(v___x_951_, v_x_934_);
if (lean_obj_tag(v___x_952_) == 1)
{
lean_object* v_val_953_; 
v_val_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_val_953_);
lean_dec_ref_known(v___x_952_, 1);
v_a_939_ = v_val_953_;
goto v___jp_938_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v___x_952_);
v___x_954_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6);
v___x_955_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_934_, v___x_954_, v_a_935_, v_a_936_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
v___jp_938_:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lake_Toml_DateTime_ofString_x3f(v_a_939_);
if (lean_obj_tag(v___x_940_) == 1)
{
lean_object* v_val_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_val_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_val_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set_tag(v___x_943_, 0);
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_val_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v___x_940_);
v___x_949_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1);
v___x_950_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_934_, v___x_949_, v_a_935_, v_a_936_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object* v_x_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_x_964_);
return v_res_968_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3));
v___x_978_ = l_Lean_MessageData_ofFormat(v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object* v_x_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_a_984_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
v___x_997_ = l_Lean_Syntax_isLit_x3f(v___x_996_, v_x_979_);
if (lean_obj_tag(v___x_997_) == 1)
{
lean_object* v_val_998_; 
v_val_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v___x_997_, 1);
v_a_984_ = v_val_998_;
goto v___jp_983_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
lean_dec(v___x_997_);
v___x_999_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4);
v___x_1000_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_979_, v___x_999_, v_a_980_, v_a_981_);
return v___x_1000_;
}
v___jp_983_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_string_utf8_byte_size(v_a_984_);
lean_inc_ref_n(v_a_984_, 2);
v___x_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_988_, 0, v_a_984_);
lean_ctor_set(v___x_988_, 1, v___x_986_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
v___x_989_ = l_String_Slice_Pos_nextn(v___x_988_, v___x_986_, v___x_985_);
lean_dec_ref_known(v___x_988_, 3);
lean_inc(v___x_989_);
v___x_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_990_, 0, v_a_984_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_ctor_set(v___x_990_, 2, v___x_987_);
v___x_991_ = lean_nat_sub(v___x_987_, v___x_989_);
v___x_992_ = l_String_Slice_Pos_prevn(v___x_990_, v___x_991_, v___x_985_);
lean_dec_ref_known(v___x_990_, 3);
v___x_993_ = lean_nat_add(v___x_989_, v___x_992_);
lean_dec(v___x_992_);
v___x_994_ = lean_string_utf8_extract_fast(v_a_984_, v___x_989_, v___x_993_);
lean_dec(v___x_993_);
lean_dec(v___x_989_);
lean_dec_ref(v_a_984_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object* v_x_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_x_1001_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object* v_msg_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = l_String_instInhabitedSlice;
v___x_1008_ = lean_panic_fn_borrowed(v___x_1007_, v_msg_1006_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object* v___y_1009_, lean_object* v_a_1010_, lean_object* v_b_1011_){
_start:
{
lean_object* v_str_1012_; lean_object* v_startInclusive_1013_; lean_object* v_endExclusive_1014_; lean_object* v___x_1015_; uint8_t v_decide_1016_; 
v_str_1012_ = lean_ctor_get(v___y_1009_, 0);
v_startInclusive_1013_ = lean_ctor_get(v___y_1009_, 1);
v_endExclusive_1014_ = lean_ctor_get(v___y_1009_, 2);
v___x_1015_ = lean_nat_sub(v_endExclusive_1014_, v_startInclusive_1013_);
v_decide_1016_ = lean_nat_dec_eq(v_a_1010_, v___x_1015_);
lean_dec(v___x_1015_);
if (v_decide_1016_ == 0)
{
lean_object* v___x_1017_; uint32_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1017_ = lean_nat_add(v_startInclusive_1013_, v_a_1010_);
lean_dec(v_a_1010_);
v___x_1018_ = lean_string_utf8_get_fast(v_str_1012_, v___x_1017_);
v___x_1019_ = lean_string_utf8_next_fast(v_str_1012_, v___x_1017_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_nat_sub(v___x_1019_, v_startInclusive_1013_);
v___x_1021_ = lean_unsigned_to_nat(16u);
v___x_1022_ = lean_nat_mul(v_b_1011_, v___x_1021_);
lean_dec(v_b_1011_);
v___x_1023_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_1018_);
v___x_1024_ = lean_nat_add(v___x_1022_, v___x_1023_);
lean_dec(v___x_1023_);
lean_dec(v___x_1022_);
v_a_1010_ = v___x_1020_;
v_b_1011_ = v___x_1024_;
goto _start;
}
else
{
lean_dec(v_a_1010_);
return v_b_1011_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object* v___y_1026_, lean_object* v_a_1027_, lean_object* v_b_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1026_, v_a_1027_, v_b_1028_);
lean_dec_ref(v___y_1026_);
return v_res_1029_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1033_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2));
v___x_1034_ = lean_unsigned_to_nat(14u);
v___x_1035_ = lean_unsigned_to_nat(22u);
v___x_1036_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1));
v___x_1037_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0));
v___x_1038_ = l_mkPanicMessageWithDecl(v___x_1037_, v___x_1036_, v___x_1035_, v___x_1034_, v___x_1033_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object* v_s_1039_){
_start:
{
lean_object* v_str_1040_; lean_object* v_startPos_1041_; lean_object* v_stopPos_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1062_; 
v_str_1040_ = lean_ctor_get(v_s_1039_, 0);
v_startPos_1041_ = lean_ctor_get(v_s_1039_, 1);
v_stopPos_1042_ = lean_ctor_get(v_s_1039_, 2);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_s_1039_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1044_ = v_s_1039_;
v_isShared_1045_ = v_isSharedCheck_1062_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_stopPos_1042_);
lean_inc(v_startPos_1041_);
lean_inc(v_str_1040_);
lean_dec(v_s_1039_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1062_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___y_1048_; uint8_t v___y_1051_; uint8_t v___x_1057_; uint8_t v___y_1059_; uint8_t v___x_1060_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_string_is_valid_pos(v_str_1040_, v_startPos_1041_);
v___x_1060_ = lean_string_is_valid_pos(v_str_1040_, v_stopPos_1042_);
if (v___x_1060_ == 0)
{
v___y_1059_ = v___x_1060_;
goto v___jp_1058_;
}
else
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_nat_dec_le(v_startPos_1041_, v_stopPos_1042_);
v___y_1059_ = v___x_1061_;
goto v___jp_1058_;
}
v___jp_1047_:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1048_, v___x_1046_, v___x_1046_);
lean_dec_ref(v___y_1048_);
return v___x_1049_;
}
v___jp_1050_:
{
if (v___y_1051_ == 0)
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
lean_del_object(v___x_1044_);
lean_dec(v_stopPos_1042_);
lean_dec(v_startPos_1041_);
lean_dec_ref(v_str_1040_);
v___x_1052_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3);
v___x_1053_ = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(v___x_1052_);
v___y_1048_ = v___x_1053_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1055_; 
if (v_isShared_1045_ == 0)
{
v___x_1055_ = v___x_1044_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_str_1040_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_startPos_1041_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_stopPos_1042_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
v___y_1048_ = v___x_1055_;
goto v___jp_1047_;
}
}
}
v___jp_1058_:
{
if (v___x_1057_ == 0)
{
v___y_1051_ = v___x_1057_;
goto v___jp_1050_;
}
else
{
v___y_1051_ = v___y_1059_;
goto v___jp_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object* v___y_1063_, lean_object* v_inst_1064_, lean_object* v_R_1065_, lean_object* v_a_1066_, lean_object* v_b_1067_, lean_object* v_c_1068_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1063_, v_a_1066_, v_b_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object* v___y_1070_, lean_object* v_inst_1071_, lean_object* v_R_1072_, lean_object* v_a_1073_, lean_object* v_b_1074_, lean_object* v_c_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(v___y_1070_, v_inst_1071_, v_R_1072_, v_a_1073_, v_b_1074_, v_c_1075_);
lean_dec_ref(v___y_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object* v_s_1077_, lean_object* v_stopPos_1078_, lean_object* v_i_1079_){
_start:
{
uint8_t v___y_1081_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1084_ = lean_unsigned_to_nat(1u);
v___x_1085_ = lean_nat_add(v_i_1079_, v___x_1084_);
v___x_1086_ = lean_nat_dec_le(v___x_1085_, v_stopPos_1078_);
lean_dec(v___x_1085_);
if (v___x_1086_ == 0)
{
return v_i_1079_;
}
else
{
if (v___x_1086_ == 0)
{
v___y_1081_ = v___x_1086_;
goto v___jp_1080_;
}
else
{
uint32_t v___x_1087_; uint32_t v___x_1088_; uint8_t v___x_1089_; 
v___x_1087_ = lean_string_utf8_get(v_s_1077_, v_i_1079_);
v___x_1088_ = 32;
v___x_1089_ = lean_uint32_dec_eq(v___x_1087_, v___x_1088_);
if (v___x_1089_ == 0)
{
uint32_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1090_ = 9;
v___x_1091_ = lean_uint32_dec_eq(v___x_1087_, v___x_1090_);
if (v___x_1091_ == 0)
{
uint32_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = 13;
v___x_1093_ = lean_uint32_dec_eq(v___x_1087_, v___x_1092_);
if (v___x_1093_ == 0)
{
uint32_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = 10;
v___x_1095_ = lean_uint32_dec_eq(v___x_1087_, v___x_1094_);
v___y_1081_ = v___x_1095_;
goto v___jp_1080_;
}
else
{
v___y_1081_ = v___x_1093_;
goto v___jp_1080_;
}
}
else
{
v___y_1081_ = v___x_1091_;
goto v___jp_1080_;
}
}
else
{
v___y_1081_ = v___x_1089_;
goto v___jp_1080_;
}
}
}
v___jp_1080_:
{
if (v___y_1081_ == 0)
{
return v_i_1079_;
}
else
{
lean_object* v___x_1082_; 
v___x_1082_ = lean_string_utf8_next(v_s_1077_, v_i_1079_);
lean_dec(v_i_1079_);
v_i_1079_ = v___x_1082_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object* v_s_1096_, lean_object* v_stopPos_1097_, lean_object* v_i_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_s_1096_, v_stopPos_1097_, v_i_1098_);
lean_dec(v_stopPos_1097_);
lean_dec_ref(v_s_1096_);
return v_res_1099_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object* v_lit_1106_, lean_object* v_i_1107_, lean_object* v_out_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1122_; uint8_t v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; uint8_t v___y_1127_; lean_object* v_escape_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; uint8_t v___x_1147_; 
v___x_1147_ = lean_string_utf8_at_end(v_lit_1106_, v_i_1107_);
if (v___x_1147_ == 0)
{
uint32_t v_curr_1148_; lean_object* v_i_1149_; uint32_t v___x_1150_; uint8_t v___x_1151_; 
v_curr_1148_ = lean_string_utf8_get_fast(v_lit_1106_, v_i_1107_);
v_i_1149_ = lean_string_utf8_next_fast(v_lit_1106_, v_i_1107_);
lean_dec(v_i_1107_);
v___x_1150_ = 92;
v___x_1151_ = lean_uint32_dec_eq(v_curr_1148_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_string_push(v_out_1108_, v_curr_1148_);
v_i_1107_ = v_i_1149_;
v_out_1108_ = v___x_1152_;
goto _start;
}
else
{
uint8_t v___x_1154_; 
v___x_1154_ = lean_string_utf8_at_end(v_lit_1106_, v_i_1149_);
if (v___x_1154_ == 0)
{
uint32_t v_curr_1155_; lean_object* v_next_1156_; uint32_t v___x_1157_; uint8_t v___x_1158_; 
v_curr_1155_ = lean_string_utf8_get_fast(v_lit_1106_, v_i_1149_);
v_next_1156_ = lean_string_utf8_next_fast(v_lit_1106_, v_i_1149_);
v___x_1157_ = 98;
v___x_1158_ = lean_uint32_dec_eq(v_curr_1155_, v___x_1157_);
if (v___x_1158_ == 0)
{
uint32_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = 116;
v___x_1160_ = lean_uint32_dec_eq(v_curr_1155_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint32_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = 110;
v___x_1162_ = lean_uint32_dec_eq(v_curr_1155_, v___x_1161_);
if (v___x_1162_ == 0)
{
uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = 102;
v___x_1164_ = lean_uint32_dec_eq(v_curr_1155_, v___x_1163_);
if (v___x_1164_ == 0)
{
uint32_t v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = 114;
v___x_1166_ = lean_uint32_dec_eq(v_curr_1155_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint32_t v___x_1167_; uint8_t v___x_1168_; 
v___x_1167_ = 34;
v___x_1168_ = lean_uint32_dec_eq(v_curr_1155_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_uint32_dec_eq(v_curr_1155_, v___x_1150_);
if (v___x_1169_ == 0)
{
uint32_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = 117;
v___x_1171_ = lean_uint32_dec_eq(v_curr_1155_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 85;
v___x_1173_ = lean_uint32_dec_eq(v_curr_1155_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; lean_object* v_b_1175_; 
v___x_1174_ = lean_string_utf8_byte_size(v_lit_1106_);
v_b_1175_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_lit_1106_, v___x_1174_, v_i_1149_);
v_i_1107_ = v_b_1175_;
goto _start;
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1177_ = lean_string_utf8_byte_size(v_lit_1106_);
lean_inc_ref_n(v_lit_1106_, 2);
v___x_1178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1178_, 0, v_lit_1106_);
lean_ctor_set(v___x_1178_, 1, v_next_1156_);
lean_ctor_set(v___x_1178_, 2, v___x_1177_);
v___x_1179_ = lean_unsigned_to_nat(8u);
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = l_Substring_Raw_nextn(v___x_1178_, v___x_1179_, v___x_1180_);
lean_dec_ref_known(v___x_1178_, 3);
v___x_1182_ = lean_nat_add(v_next_1156_, v___x_1181_);
lean_dec(v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1183_, 0, v_lit_1106_);
lean_ctor_set(v___x_1183_, 1, v_next_1156_);
lean_ctor_set(v___x_1183_, 2, v___x_1182_);
v_escape_1137_ = v___x_1183_;
v___y_1138_ = v_a_1109_;
v___y_1139_ = v_a_1110_;
goto v___jp_1136_;
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1184_ = lean_string_utf8_byte_size(v_lit_1106_);
lean_inc_ref_n(v_lit_1106_, 2);
v___x_1185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1185_, 0, v_lit_1106_);
lean_ctor_set(v___x_1185_, 1, v_next_1156_);
lean_ctor_set(v___x_1185_, 2, v___x_1184_);
v___x_1186_ = lean_unsigned_to_nat(4u);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = l_Substring_Raw_nextn(v___x_1185_, v___x_1186_, v___x_1187_);
lean_dec_ref_known(v___x_1185_, 3);
v___x_1189_ = lean_nat_add(v_next_1156_, v___x_1188_);
lean_dec(v___x_1188_);
v___x_1190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1190_, 0, v_lit_1106_);
lean_ctor_set(v___x_1190_, 1, v_next_1156_);
lean_ctor_set(v___x_1190_, 2, v___x_1189_);
v_escape_1137_ = v___x_1190_;
v___y_1138_ = v_a_1109_;
v___y_1139_ = v_a_1110_;
goto v___jp_1136_;
}
}
else
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_string_push(v_out_1108_, v___x_1150_);
v_i_1107_ = v_next_1156_;
v_out_1108_ = v___x_1191_;
goto _start;
}
}
else
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_string_push(v_out_1108_, v___x_1167_);
v_i_1107_ = v_next_1156_;
v_out_1108_ = v___x_1193_;
goto _start;
}
}
else
{
uint32_t v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = 13;
v___x_1196_ = lean_string_push(v_out_1108_, v___x_1195_);
v_i_1107_ = v_next_1156_;
v_out_1108_ = v___x_1196_;
goto _start;
}
}
else
{
uint32_t v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = 12;
v___x_1199_ = lean_string_push(v_out_1108_, v___x_1198_);
v_i_1107_ = v_next_1156_;
v_out_1108_ = v___x_1199_;
goto _start;
}
}
else
{
uint32_t v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = 10;
v___x_1202_ = lean_string_push(v_out_1108_, v___x_1201_);
v_i_1107_ = v_next_1156_;
v_out_1108_ = v___x_1202_;
goto _start;
}
}
else
{
uint32_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = 9;
v___x_1205_ = lean_string_push(v_out_1108_, v___x_1204_);
v_i_1107_ = v_next_1156_;
v_out_1108_ = v___x_1205_;
goto _start;
}
}
else
{
uint32_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = 8;
v___x_1208_ = lean_string_push(v_out_1108_, v___x_1207_);
v_i_1107_ = v_next_1156_;
v_out_1108_ = v___x_1208_;
goto _start;
}
}
else
{
lean_object* v___x_1210_; 
lean_dec_ref(v_lit_1106_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_out_1108_);
return v___x_1210_;
}
}
}
else
{
lean_object* v___x_1211_; 
lean_dec(v_i_1107_);
lean_dec_ref(v_lit_1106_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_out_1108_);
return v___x_1211_;
}
v___jp_1112_:
{
lean_object* v_stopPos_1117_; uint32_t v_ch_1118_; lean_object* v___x_1119_; 
v_stopPos_1117_ = lean_ctor_get(v___y_1116_, 2);
lean_inc(v_stopPos_1117_);
lean_dec_ref(v___y_1116_);
v_ch_1118_ = lean_uint32_of_nat(v___y_1115_);
lean_dec(v___y_1115_);
v___x_1119_ = lean_string_push(v_out_1108_, v_ch_1118_);
v_i_1107_ = v_stopPos_1117_;
v_out_1108_ = v___x_1119_;
v_a_1109_ = v___y_1113_;
v_a_1110_ = v___y_1114_;
goto _start;
}
v___jp_1121_:
{
if (v___y_1123_ == 0)
{
if (v___y_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v___y_1125_);
lean_dec_ref(v_out_1108_);
lean_dec_ref(v_lit_1106_);
v___x_1128_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1);
v___x_1129_ = lean_substring_tostring(v___y_1126_);
v___x_1130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
v___x_1131_ = l_Lean_MessageData_ofFormat(v___x_1130_);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1128_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v___x_1134_, v___y_1122_, v___y_1124_);
return v___x_1135_;
}
else
{
v___y_1113_ = v___y_1122_;
v___y_1114_ = v___y_1124_;
v___y_1115_ = v___y_1125_;
v___y_1116_ = v___y_1126_;
goto v___jp_1112_;
}
}
else
{
v___y_1113_ = v___y_1122_;
v___y_1114_ = v___y_1124_;
v___y_1115_ = v___y_1125_;
v___y_1116_ = v___y_1126_;
goto v___jp_1112_;
}
}
v___jp_1136_:
{
lean_object* v_val_1140_; lean_object* v___x_1141_; uint8_t v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
lean_inc_ref(v_escape_1137_);
v_val_1140_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(v_escape_1137_);
v___x_1141_ = lean_unsigned_to_nat(55296u);
v___x_1142_ = lean_nat_dec_lt(v_val_1140_, v___x_1141_);
v___x_1143_ = lean_unsigned_to_nat(57343u);
v___x_1144_ = lean_nat_dec_lt(v___x_1143_, v_val_1140_);
if (v___x_1144_ == 0)
{
v___y_1122_ = v___y_1138_;
v___y_1123_ = v___x_1142_;
v___y_1124_ = v___y_1139_;
v___y_1125_ = v_val_1140_;
v___y_1126_ = v_escape_1137_;
v___y_1127_ = v___x_1144_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1145_; uint8_t v___x_1146_; 
v___x_1145_ = lean_unsigned_to_nat(1114112u);
v___x_1146_ = lean_nat_dec_lt(v_val_1140_, v___x_1145_);
v___y_1122_ = v___y_1138_;
v___y_1123_ = v___x_1142_;
v___y_1124_ = v___y_1139_;
v___y_1125_ = v_val_1140_;
v___y_1126_ = v_escape_1137_;
v___y_1127_ = v___x_1146_;
goto v___jp_1121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object* v_lit_1212_, lean_object* v_i_1213_, lean_object* v_out_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v_lit_1212_, v_i_1213_, v_out_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
return v_res_1218_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4));
v___x_1229_ = l_Lean_MessageData_ofFormat(v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object* v_x_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_a_1235_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
v___x_1256_ = l_Lean_Syntax_isLit_x3f(v___x_1255_, v_x_1230_);
if (lean_obj_tag(v___x_1256_) == 1)
{
lean_object* v_val_1257_; 
v_val_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_val_1257_);
lean_dec_ref_known(v___x_1256_, 1);
v_a_1235_ = v_val_1257_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v___x_1256_);
v___x_1258_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5);
v___x_1259_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1230_, v___x_1258_, v_a_1231_, v_a_1232_);
return v___x_1259_;
}
v___jp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_toCold_1239_; lean_object* v_currRecDepth_1240_; lean_object* v_ref_1241_; uint8_t v_diag_1242_; uint8_t v_suppressElabErrors_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v_ref_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_string_utf8_byte_size(v_a_1235_);
lean_inc_ref_n(v_a_1235_, 2);
v___x_1238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1238_, 0, v_a_1235_);
lean_ctor_set(v___x_1238_, 1, v___x_1236_);
lean_ctor_set(v___x_1238_, 2, v___x_1237_);
v_toCold_1239_ = lean_ctor_get(v_a_1231_, 0);
v_currRecDepth_1240_ = lean_ctor_get(v_a_1231_, 1);
v_ref_1241_ = lean_ctor_get(v_a_1231_, 2);
v_diag_1242_ = lean_ctor_get_uint8(v_a_1231_, sizeof(void*)*3);
v_suppressElabErrors_1243_ = lean_ctor_get_uint8(v_a_1231_, sizeof(void*)*3 + 1);
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = l_String_Slice_Pos_nextn(v___x_1238_, v___x_1236_, v___x_1244_);
lean_dec_ref_known(v___x_1238_, 3);
lean_inc(v___x_1245_);
v___x_1246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1246_, 0, v_a_1235_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
lean_ctor_set(v___x_1246_, 2, v___x_1237_);
v___x_1247_ = lean_nat_sub(v___x_1237_, v___x_1245_);
v___x_1248_ = l_String_Slice_Pos_prevn(v___x_1246_, v___x_1247_, v___x_1244_);
lean_dec_ref_known(v___x_1246_, 3);
v___x_1249_ = lean_nat_add(v___x_1245_, v___x_1248_);
lean_dec(v___x_1248_);
v___x_1250_ = lean_string_utf8_extract_fast(v_a_1235_, v___x_1245_, v___x_1249_);
lean_dec(v___x_1249_);
lean_dec(v___x_1245_);
lean_dec_ref(v_a_1235_);
v___x_1251_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1252_ = l_Lean_replaceRef(v_x_1230_, v_ref_1241_);
lean_inc(v_currRecDepth_1240_);
lean_inc_ref(v_toCold_1239_);
v___x_1253_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1253_, 0, v_toCold_1239_);
lean_ctor_set(v___x_1253_, 1, v_currRecDepth_1240_);
lean_ctor_set(v___x_1253_, 2, v_ref_1252_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*3, v_diag_1242_);
lean_ctor_set_uint8(v___x_1253_, sizeof(void*)*3 + 1, v_suppressElabErrors_1243_);
v___x_1254_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1250_, v___x_1236_, v___x_1251_, v___x_1253_, v_a_1232_);
lean_dec_ref_known(v___x_1253_, 3);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object* v_x_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1260_, v_a_1261_, v_a_1262_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_x_1260_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object* v_s_1265_){
_start:
{
uint32_t v___y_1267_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_string_utf8_byte_size(v_s_1265_);
lean_inc_ref(v_s_1265_);
v___x_1286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1286_, 0, v_s_1265_);
lean_ctor_set(v___x_1286_, 1, v___x_1284_);
lean_ctor_set(v___x_1286_, 2, v___x_1285_);
v___x_1287_ = l_String_Slice_Pos_get_x3f(v___x_1286_, v___x_1284_);
lean_dec_ref_known(v___x_1286_, 3);
if (lean_obj_tag(v___x_1287_) == 0)
{
uint32_t v___x_1288_; 
v___x_1288_ = 65;
v___y_1267_ = v___x_1288_;
goto v___jp_1266_;
}
else
{
lean_object* v_val_1289_; uint32_t v___x_1290_; 
v_val_1289_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_val_1289_);
lean_dec_ref_known(v___x_1287_, 1);
v___x_1290_ = lean_unbox_uint32(v_val_1289_);
lean_dec(v_val_1289_);
v___y_1267_ = v___x_1290_;
goto v___jp_1266_;
}
v___jp_1266_:
{
uint32_t v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = 13;
v___x_1269_ = lean_uint32_dec_eq(v___y_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
uint32_t v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = 10;
v___x_1271_ = lean_uint32_dec_eq(v___y_1267_, v___x_1270_);
if (v___x_1271_ == 0)
{
return v_s_1265_;
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_string_utf8_byte_size(v_s_1265_);
lean_inc_ref(v_s_1265_);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v_s_1265_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
lean_ctor_set(v___x_1275_, 2, v___x_1274_);
v___x_1276_ = l_String_Slice_Pos_nextn(v___x_1275_, v___x_1273_, v___x_1272_);
lean_dec_ref_known(v___x_1275_, 3);
v___x_1277_ = lean_string_utf8_extract_fast(v_s_1265_, v___x_1276_, v___x_1274_);
lean_dec(v___x_1276_);
lean_dec_ref(v_s_1265_);
return v___x_1277_;
}
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1278_ = lean_unsigned_to_nat(2u);
v___x_1279_ = lean_unsigned_to_nat(0u);
v___x_1280_ = lean_string_utf8_byte_size(v_s_1265_);
lean_inc_ref(v_s_1265_);
v___x_1281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1281_, 0, v_s_1265_);
lean_ctor_set(v___x_1281_, 1, v___x_1279_);
lean_ctor_set(v___x_1281_, 2, v___x_1280_);
v___x_1282_ = l_String_Slice_Pos_nextn(v___x_1281_, v___x_1279_, v___x_1278_);
lean_dec_ref_known(v___x_1281_, 3);
v___x_1283_ = lean_string_utf8_extract_fast(v_s_1265_, v___x_1282_, v___x_1280_);
lean_dec(v___x_1282_);
lean_dec_ref(v_s_1265_);
return v___x_1283_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3));
v___x_1300_ = l_Lean_MessageData_ofFormat(v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object* v_x_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_a_1306_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
v___x_1320_ = l_Lean_Syntax_isLit_x3f(v___x_1319_, v_x_1301_);
if (lean_obj_tag(v___x_1320_) == 1)
{
lean_object* v_val_1321_; 
v_val_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_val_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v_a_1306_ = v_val_1321_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v___x_1320_);
v___x_1322_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4);
v___x_1323_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1301_, v___x_1322_, v_a_1302_, v_a_1303_);
return v___x_1323_;
}
v___jp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1307_ = lean_unsigned_to_nat(3u);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_string_utf8_byte_size(v_a_1306_);
lean_inc_ref_n(v_a_1306_, 2);
v___x_1310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1310_, 0, v_a_1306_);
lean_ctor_set(v___x_1310_, 1, v___x_1308_);
lean_ctor_set(v___x_1310_, 2, v___x_1309_);
v___x_1311_ = l_String_Slice_Pos_nextn(v___x_1310_, v___x_1308_, v___x_1307_);
lean_dec_ref_known(v___x_1310_, 3);
lean_inc(v___x_1311_);
v___x_1312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1312_, 0, v_a_1306_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
lean_ctor_set(v___x_1312_, 2, v___x_1309_);
v___x_1313_ = lean_nat_sub(v___x_1309_, v___x_1311_);
v___x_1314_ = l_String_Slice_Pos_prevn(v___x_1312_, v___x_1313_, v___x_1307_);
lean_dec_ref_known(v___x_1312_, 3);
v___x_1315_ = lean_nat_add(v___x_1311_, v___x_1314_);
lean_dec(v___x_1314_);
v___x_1316_ = lean_string_utf8_extract_fast(v_a_1306_, v___x_1311_, v___x_1315_);
lean_dec(v___x_1315_);
lean_dec(v___x_1311_);
lean_dec_ref(v_a_1306_);
v___x_1317_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1316_);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object* v_x_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1324_, v_a_1325_, v_a_1326_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_x_1324_);
return v_res_1328_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3));
v___x_1338_ = l_Lean_MessageData_ofFormat(v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object* v_x_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_a_1344_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
v___x_1366_ = l_Lean_Syntax_isLit_x3f(v___x_1365_, v_x_1339_);
if (lean_obj_tag(v___x_1366_) == 1)
{
lean_object* v_val_1367_; 
v_val_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v_a_1344_ = v_val_1367_;
goto v___jp_1343_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v___x_1366_);
v___x_1368_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4);
v___x_1369_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1339_, v___x_1368_, v_a_1340_, v_a_1341_);
return v___x_1369_;
}
v___jp_1343_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v_toCold_1348_; lean_object* v_currRecDepth_1349_; lean_object* v_ref_1350_; uint8_t v_diag_1351_; uint8_t v_suppressElabErrors_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_ref_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_string_utf8_byte_size(v_a_1344_);
lean_inc_ref_n(v_a_1344_, 2);
v___x_1347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1347_, 0, v_a_1344_);
lean_ctor_set(v___x_1347_, 1, v___x_1345_);
lean_ctor_set(v___x_1347_, 2, v___x_1346_);
v_toCold_1348_ = lean_ctor_get(v_a_1340_, 0);
v_currRecDepth_1349_ = lean_ctor_get(v_a_1340_, 1);
v_ref_1350_ = lean_ctor_get(v_a_1340_, 2);
v_diag_1351_ = lean_ctor_get_uint8(v_a_1340_, sizeof(void*)*3);
v_suppressElabErrors_1352_ = lean_ctor_get_uint8(v_a_1340_, sizeof(void*)*3 + 1);
v___x_1353_ = lean_unsigned_to_nat(3u);
v___x_1354_ = l_String_Slice_Pos_nextn(v___x_1347_, v___x_1345_, v___x_1353_);
lean_dec_ref_known(v___x_1347_, 3);
lean_inc(v___x_1354_);
v___x_1355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1355_, 0, v_a_1344_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
lean_ctor_set(v___x_1355_, 2, v___x_1346_);
v___x_1356_ = lean_nat_sub(v___x_1346_, v___x_1354_);
v___x_1357_ = l_String_Slice_Pos_prevn(v___x_1355_, v___x_1356_, v___x_1353_);
lean_dec_ref_known(v___x_1355_, 3);
v___x_1358_ = lean_nat_add(v___x_1354_, v___x_1357_);
lean_dec(v___x_1357_);
v___x_1359_ = lean_string_utf8_extract_fast(v_a_1344_, v___x_1354_, v___x_1358_);
lean_dec(v___x_1358_);
lean_dec(v___x_1354_);
lean_dec_ref(v_a_1344_);
v___x_1360_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1359_);
v___x_1361_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1362_ = l_Lean_replaceRef(v_x_1339_, v_ref_1350_);
lean_inc(v_currRecDepth_1349_);
lean_inc_ref(v_toCold_1348_);
v___x_1363_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1363_, 0, v_toCold_1348_);
lean_ctor_set(v___x_1363_, 1, v_currRecDepth_1349_);
lean_ctor_set(v___x_1363_, 2, v_ref_1362_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*3, v_diag_1351_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*3 + 1, v_suppressElabErrors_1352_);
v___x_1364_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1360_, v___x_1345_, v___x_1361_, v___x_1363_, v_a_1341_);
lean_dec_ref_known(v___x_1363_, 3);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object* v_x_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_x_1370_);
return v_res_1374_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2));
v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object* v_x_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_1383_);
v___x_1388_ = l_Lean_Syntax_isOfKind(v_x_1383_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1390_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1383_, v___x_1389_, v_a_1384_, v_a_1385_);
lean_dec(v_x_1383_);
return v___x_1390_;
}
else
{
lean_object* v___x_1391_; lean_object* v_x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1391_ = lean_unsigned_to_nat(0u);
v_x_1392_ = l_Lean_Syntax_getArg(v_x_1383_, v___x_1391_);
v___x_1393_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1392_);
v___x_1394_ = l_Lean_Syntax_isOfKind(v_x_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1392_);
v___x_1396_ = l_Lean_Syntax_isOfKind(v_x_1392_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
lean_inc(v_x_1392_);
v___x_1398_ = l_Lean_Syntax_isOfKind(v_x_1392_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1399_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
lean_inc(v_x_1392_);
v___x_1400_ = l_Lean_Syntax_isOfKind(v_x_1392_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec(v_x_1392_);
v___x_1401_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1402_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1383_, v___x_1401_, v_a_1384_, v_a_1385_);
lean_dec(v_x_1383_);
return v___x_1402_;
}
else
{
lean_object* v___x_1403_; 
lean_dec(v_x_1383_);
v___x_1403_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1392_, v_a_1384_, v_a_1385_);
lean_dec(v_x_1392_);
return v___x_1403_;
}
}
else
{
lean_object* v___x_1404_; 
lean_dec(v_x_1383_);
v___x_1404_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1392_, v_a_1384_, v_a_1385_);
lean_dec(v_x_1392_);
return v___x_1404_;
}
}
else
{
lean_object* v___x_1405_; 
lean_dec(v_x_1383_);
v___x_1405_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1392_, v_a_1384_, v_a_1385_);
lean_dec(v_x_1392_);
return v___x_1405_;
}
}
else
{
lean_object* v___x_1406_; 
lean_dec(v_x_1383_);
v___x_1406_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1392_, v_a_1384_, v_a_1385_);
lean_dec(v_x_1392_);
return v___x_1406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object* v_x_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
return v_res_1411_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3));
v___x_1421_ = l_Lean_MessageData_ofFormat(v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object* v_x_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v___x_1426_; lean_object* v_toApplicative_1427_; lean_object* v_toFunctor_1428_; lean_object* v_toSeq_1429_; lean_object* v_toSeqLeft_1430_; lean_object* v_toSeqRight_1431_; lean_object* v___x_1432_; lean_object* v___f_1433_; lean_object* v___f_1434_; lean_object* v___f_1435_; lean_object* v___f_1436_; lean_object* v___x_1437_; lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1426_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_1427_ = lean_ctor_get(v___x_1426_, 0);
v_toFunctor_1428_ = lean_ctor_get(v_toApplicative_1427_, 0);
v_toSeq_1429_ = lean_ctor_get(v_toApplicative_1427_, 2);
v_toSeqLeft_1430_ = lean_ctor_get(v_toApplicative_1427_, 3);
v_toSeqRight_1431_ = lean_ctor_get(v_toApplicative_1427_, 4);
v___x_1432_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
v___f_1433_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_1434_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref_n(v_toFunctor_1428_, 2);
v___f_1435_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1435_, 0, v_toFunctor_1428_);
v___f_1436_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1436_, 0, v_toFunctor_1428_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___f_1435_);
lean_ctor_set(v___x_1437_, 1, v___f_1436_);
lean_inc(v_toSeqRight_1431_);
v___f_1438_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1438_, 0, v_toSeqRight_1431_);
lean_inc(v_toSeqLeft_1430_);
v___f_1439_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1439_, 0, v_toSeqLeft_1430_);
lean_inc(v_toSeq_1429_);
v___f_1440_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1440_, 0, v_toSeq_1429_);
v___x_1441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1437_);
lean_ctor_set(v___x_1441_, 1, v___f_1433_);
lean_ctor_set(v___x_1441_, 2, v___f_1440_);
lean_ctor_set(v___x_1441_, 3, v___f_1439_);
lean_ctor_set(v___x_1441_, 4, v___f_1438_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v___f_1434_);
v___x_1443_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_1444_ = l_Lean_Core_instMonadRefCoreM;
v___x_1445_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_1442_);
v___x_1446_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1445_, v___x_1442_);
v___x_1447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1443_);
lean_ctor_set(v___x_1447_, 1, v___x_1444_);
lean_ctor_set(v___x_1447_, 2, v___x_1446_);
v___x_1448_ = l_Lean_Syntax_isLit_x3f(v___x_1432_, v_x_1422_);
if (lean_obj_tag(v___x_1448_) == 1)
{
lean_object* v_val_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref_known(v___x_1447_, 3);
lean_dec_ref_known(v___x_1442_, 2);
lean_dec(v_x_1422_);
v_val_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_val_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set_tag(v___x_1451_, 0);
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_val_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
else
{
lean_object* v___x_1457_; lean_object* v___x_40__overap_1458_; lean_object* v___x_1459_; 
lean_dec(v___x_1448_);
v___x_1457_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_40__overap_1458_ = l_Lean_throwErrorAt___redArg(v___x_1442_, v___x_1447_, v_x_1422_, v___x_1457_);
lean_inc(v_a_1424_);
lean_inc_ref(v_a_1423_);
v___x_1459_ = lean_apply_3(v___x_40__overap_1458_, v_a_1423_, v_a_1424_, lean_box(0));
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object* v_x_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(v_x_1460_, v_a_1461_, v_a_1462_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
return v_res_1464_;
}
}
static lean_object* _init_l_Lake_Toml_elabSimpleKey___closed__3(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__2));
v___x_1472_ = l_Lean_stringToMessageData(v___x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object* v_x_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__1));
lean_inc(v_x_1473_);
v___x_1478_ = l_Lean_Syntax_isOfKind(v_x_1473_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1480_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1473_, v___x_1479_, v_a_1474_, v_a_1475_);
lean_dec(v_x_1473_);
return v___x_1480_;
}
else
{
lean_object* v___x_1481_; lean_object* v_x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1481_ = lean_unsigned_to_nat(0u);
v_x_1482_ = l_Lean_Syntax_getArg(v_x_1473_, v___x_1481_);
v___x_1483_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
lean_inc(v_x_1482_);
v___x_1484_ = l_Lean_Syntax_isOfKind(v_x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; uint8_t v___x_1486_; 
v___x_1485_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1482_);
v___x_1486_ = l_Lean_Syntax_isOfKind(v_x_1482_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1487_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1482_);
v___x_1488_ = l_Lean_Syntax_isOfKind(v_x_1482_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec(v_x_1482_);
v___x_1489_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1490_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1473_, v___x_1489_, v_a_1474_, v_a_1475_);
lean_dec(v_x_1473_);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v_x_1473_);
v___x_1491_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1482_, v_a_1474_, v_a_1475_);
lean_dec(v_x_1482_);
return v___x_1491_;
}
}
else
{
lean_object* v___x_1492_; 
lean_dec(v_x_1473_);
v___x_1492_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1482_, v_a_1474_, v_a_1475_);
lean_dec(v_x_1482_);
return v___x_1492_;
}
}
else
{
lean_object* v___x_1493_; 
lean_dec(v_x_1473_);
v___x_1493_ = l_Lean_Syntax_isLit_x3f(v___x_1483_, v_x_1482_);
if (lean_obj_tag(v___x_1493_) == 1)
{
lean_object* v_val_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_x_1482_);
v_val_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_val_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 0);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_val_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec(v___x_1493_);
v___x_1502_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_1503_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1482_, v___x_1502_, v_a_1474_, v_a_1475_);
lean_dec(v_x_1482_);
return v___x_1503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object* v_x_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lake_Toml_elabSimpleKey(v_x_1504_, v_a_1505_, v_a_1506_);
lean_dec(v_a_1506_);
lean_dec_ref(v_a_1505_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object* v_elabVal_1509_, size_t v_sz_1510_, size_t v_i_1511_, lean_object* v_bs_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_usize_dec_lt(v_i_1511_, v_sz_1510_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_dec_ref(v_elabVal_1509_);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_bs_1512_);
return v___x_1517_;
}
else
{
lean_object* v_v_1518_; lean_object* v___x_1519_; lean_object* v_bs_x27_1520_; lean_object* v___x_1521_; 
v_v_1518_ = lean_array_uget(v_bs_1512_, v_i_1511_);
v___x_1519_ = lean_unsigned_to_nat(0u);
v_bs_x27_1520_ = lean_array_uset(v_bs_1512_, v_i_1511_, v___x_1519_);
lean_inc_ref(v_elabVal_1509_);
lean_inc(v___y_1514_);
lean_inc_ref(v___y_1513_);
v___x_1521_ = lean_apply_4(v_elabVal_1509_, v_v_1518_, v___y_1513_, v___y_1514_, lean_box(0));
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; size_t v___x_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1521_, 1);
v___x_1523_ = ((size_t)1ULL);
v___x_1524_ = lean_usize_add(v_i_1511_, v___x_1523_);
v___x_1525_ = lean_array_uset(v_bs_x27_1520_, v_i_1511_, v_a_1522_);
v_i_1511_ = v___x_1524_;
v_bs_1512_ = v___x_1525_;
goto _start;
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v_bs_x27_1520_);
lean_dec_ref(v_elabVal_1509_);
v_a_1527_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1521_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1521_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object* v_elabVal_1535_, lean_object* v_sz_1536_, lean_object* v_i_1537_, lean_object* v_bs_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
size_t v_sz_boxed_1542_; size_t v_i_boxed_1543_; lean_object* v_res_1544_; 
v_sz_boxed_1542_ = lean_unbox_usize(v_sz_1536_);
lean_dec(v_sz_1536_);
v_i_boxed_1543_ = lean_unbox_usize(v_i_1537_);
lean_dec(v_i_1537_);
v_res_1544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1535_, v_sz_boxed_1542_, v_i_boxed_1543_, v_bs_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
return v_res_1544_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2));
v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object* v_x_1553_, lean_object* v_elabVal_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_1553_);
v___x_1559_ = l_Lean_Syntax_isOfKind(v_x_1553_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec_ref(v_elabVal_1554_);
v___x_1560_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3);
v___x_1561_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1553_, v___x_1560_, v_a_1555_, v_a_1556_);
lean_dec(v_x_1553_);
return v___x_1561_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_xs_1564_; lean_object* v___x_1565_; size_t v_sz_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = l_Lean_Syntax_getArg(v_x_1553_, v___x_1562_);
lean_dec(v_x_1553_);
v_xs_1564_ = l_Lean_Syntax_getArgs(v___x_1563_);
lean_dec(v___x_1563_);
v___x_1565_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1564_);
lean_dec_ref(v_xs_1564_);
v_sz_1566_ = lean_array_size(v___x_1565_);
v___x_1567_ = ((size_t)0ULL);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1554_, v_sz_1566_, v___x_1567_, v___x_1565_, v_a_1555_, v_a_1556_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object* v_x_1569_, lean_object* v_elabVal_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1569_, v_elabVal_1570_, v_a_1571_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object* v_00_u03b1_1575_, lean_object* v_x_1576_, lean_object* v_elabVal_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1576_, v_elabVal_1577_, v_a_1578_, v_a_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object* v_00_u03b1_1582_, lean_object* v_x_1583_, lean_object* v_elabVal_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(v_00_u03b1_1582_, v_x_1583_, v_elabVal_1584_, v_a_1585_, v_a_1586_);
lean_dec(v_a_1586_);
lean_dec_ref(v_a_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object* v_00_u03b1_1589_, lean_object* v_elabVal_1590_, size_t v_sz_1591_, size_t v_i_1592_, lean_object* v_bs_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1590_, v_sz_1591_, v_i_1592_, v_bs_1593_, v___y_1594_, v___y_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object* v_00_u03b1_1598_, lean_object* v_elabVal_1599_, lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_bs_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
size_t v_sz_boxed_1606_; size_t v_i_boxed_1607_; lean_object* v_res_1608_; 
v_sz_boxed_1606_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1607_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(v_00_u03b1_1598_, v_elabVal_1599_, v_sz_boxed_1606_, v_i_boxed_1607_, v_bs_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(size_t v_sz_1609_, size_t v_i_1610_, lean_object* v_bs_1611_){
_start:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_usize_dec_lt(v_i_1610_, v_sz_1609_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_bs_1611_);
return v___x_1613_;
}
else
{
lean_object* v_v_1614_; lean_object* v___x_1615_; lean_object* v_bs_x27_1616_; size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v_v_1614_ = lean_array_uget(v_bs_1611_, v_i_1610_);
v___x_1615_ = lean_unsigned_to_nat(0u);
v_bs_x27_1616_ = lean_array_uset(v_bs_1611_, v_i_1610_, v___x_1615_);
v___x_1617_ = ((size_t)1ULL);
v___x_1618_ = lean_usize_add(v_i_1610_, v___x_1617_);
v___x_1619_ = lean_array_uset(v_bs_x27_1616_, v_i_1610_, v_v_1614_);
v_i_1610_ = v___x_1618_;
v_bs_1611_ = v___x_1619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object* v_sz_1621_, lean_object* v_i_1622_, lean_object* v_bs_1623_){
_start:
{
size_t v_sz_boxed_1624_; size_t v_i_boxed_1625_; lean_object* v_res_1626_; 
v_sz_boxed_1624_ = lean_unbox_usize(v_sz_1621_);
lean_dec(v_sz_1621_);
v_i_boxed_1625_ = lean_unbox_usize(v_i_1622_);
lean_dec(v_i_1622_);
v_res_1626_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_sz_boxed_1624_, v_i_boxed_1625_, v_bs_1623_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(lean_object* v_msg_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_ref_1631_; lean_object* v___x_1632_; lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1641_; 
v_ref_1631_ = lean_ctor_get(v___y_1628_, 2);
v___x_1632_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_1627_, v___y_1628_, v___y_1629_);
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1635_ = v___x_1632_;
v_isShared_1636_ = v_isSharedCheck_1641_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1632_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1641_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
lean_inc(v_ref_1631_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_ref_1631_);
lean_ctor_set(v___x_1637_, 1, v_a_1633_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 0, v___x_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(lean_object* v_ref_1647_, lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_toCold_1653_; lean_object* v_currRecDepth_1654_; lean_object* v_ref_1655_; uint8_t v_diag_1656_; uint8_t v_suppressElabErrors_1657_; lean_object* v_ref_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_toCold_1653_ = lean_ctor_get(v___y_1650_, 0);
v_currRecDepth_1654_ = lean_ctor_get(v___y_1650_, 1);
v_ref_1655_ = lean_ctor_get(v___y_1650_, 2);
v_diag_1656_ = lean_ctor_get_uint8(v___y_1650_, sizeof(void*)*3);
v_suppressElabErrors_1657_ = lean_ctor_get_uint8(v___y_1650_, sizeof(void*)*3 + 1);
v_ref_1658_ = l_Lean_replaceRef(v_ref_1647_, v_ref_1655_);
lean_inc(v_currRecDepth_1654_);
lean_inc_ref(v_toCold_1653_);
v___x_1659_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1659_, 0, v_toCold_1653_);
lean_ctor_set(v___x_1659_, 1, v_currRecDepth_1654_);
lean_ctor_set(v___x_1659_, 2, v_ref_1658_);
lean_ctor_set_uint8(v___x_1659_, sizeof(void*)*3, v_diag_1656_);
lean_ctor_set_uint8(v___x_1659_, sizeof(void*)*3 + 1, v_suppressElabErrors_1657_);
v___x_1660_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_1648_, v___x_1659_, v___y_1651_);
lean_dec_ref_known(v___x_1659_, 3);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg___boxed(lean_object* v_ref_1661_, lean_object* v_msg_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v_ref_1661_, v_msg_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v_ref_1661_);
return v_res_1667_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1));
v___x_1671_ = l_Lean_stringToMessageData(v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object* v_t_1672_, uint8_t v___x_1673_, lean_object* v_as_1674_, size_t v_i_1675_, size_t v_stop_1676_, lean_object* v_b_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_fst_1683_; lean_object* v_snd_1684_; uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_eq(v_i_1675_, v_stop_1676_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1690_ = lean_array_uget_borrowed(v_as_1674_, v_i_1675_);
lean_inc(v___x_1690_);
v___x_1691_ = l_Lake_Toml_elabSimpleKey(v___x_1690_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1693_; lean_object* v___x_1711_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1691_, 1);
v___x_1693_ = l_Lean_Name_str___override(v_b_1677_, v_a_1692_);
lean_inc_ref(v_t_1672_);
lean_inc(v___x_1693_);
v___x_1711_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1689_, v___x_1693_, v_t_1672_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_box(0);
lean_inc(v___x_1693_);
v___x_1713_ = l_Lake_Toml_RBDict_push___redArg(v___x_1689_, v___x_1693_, v___x_1712_, v___y_1678_);
v_fst_1683_ = v___x_1693_;
v_snd_1684_ = v___x_1713_;
goto v___jp_1682_;
}
else
{
lean_object* v_val_1714_; lean_object* v_snd_1715_; 
v_val_1714_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_val_1714_);
lean_dec_ref_known(v___x_1711_, 1);
v_snd_1715_ = lean_ctor_get(v_val_1714_, 1);
lean_inc(v_snd_1715_);
lean_dec(v_val_1714_);
if (lean_obj_tag(v_snd_1715_) == 0)
{
if (v___x_1673_ == 0)
{
goto v___jp_1694_;
}
else
{
v_fst_1683_ = v___x_1693_;
v_snd_1684_ = v___y_1678_;
goto v___jp_1682_;
}
}
else
{
lean_dec_ref_known(v_snd_1715_, 1);
goto v___jp_1694_;
}
}
v___jp_1694_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1695_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
lean_inc(v___x_1693_);
v___x_1696_ = l_Lean_MessageData_ofName(v___x_1693_);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1697_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v___x_1690_, v___x_1699_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec_ref(v___y_1678_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v_snd_1702_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v_snd_1702_ = lean_ctor_get(v_a_1701_, 1);
lean_inc(v_snd_1702_);
lean_dec(v_a_1701_);
v_fst_1683_ = v___x_1693_;
v_snd_1684_ = v_snd_1702_;
goto v___jp_1682_;
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec(v___x_1693_);
lean_dec_ref(v_t_1672_);
v_a_1703_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1700_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1700_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref(v___y_1678_);
lean_dec(v_b_1677_);
lean_dec_ref(v_t_1672_);
v_a_1716_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1691_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1691_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec_ref(v_t_1672_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_b_1677_);
lean_ctor_set(v___x_1724_, 1, v___y_1678_);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
v___jp_1682_:
{
size_t v___x_1685_; size_t v___x_1686_; 
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1675_, v___x_1685_);
v_i_1675_ = v___x_1686_;
v_b_1677_ = v_fst_1683_;
v___y_1678_ = v_snd_1684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object* v_t_1726_, lean_object* v___x_1727_, lean_object* v_as_1728_, lean_object* v_i_1729_, lean_object* v_stop_1730_, lean_object* v_b_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
uint8_t v___x_7022__boxed_1736_; size_t v_i_boxed_1737_; size_t v_stop_boxed_1738_; lean_object* v_res_1739_; 
v___x_7022__boxed_1736_ = lean_unbox(v___x_1727_);
v_i_boxed_1737_ = lean_unbox_usize(v_i_1729_);
lean_dec(v_i_1729_);
v_stop_boxed_1738_ = lean_unbox_usize(v_stop_1730_);
lean_dec(v_stop_1730_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_t_1726_, v___x_7022__boxed_1736_, v_as_1728_, v_i_boxed_1737_, v_stop_boxed_1738_, v_b_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v_as_1728_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t v___x_1740_, lean_object* v_as_1741_, size_t v_i_1742_, size_t v_stop_1743_, lean_object* v_b_1744_){
_start:
{
lean_object* v___y_1746_; uint8_t v___x_1750_; 
v___x_1750_ = lean_usize_dec_eq(v_i_1742_, v_stop_1743_);
if (v___x_1750_ == 0)
{
lean_object* v_fst_1751_; uint8_t v___x_1752_; 
v_fst_1751_ = lean_ctor_get(v_b_1744_, 0);
v___x_1752_ = lean_unbox(v_fst_1751_);
if (v___x_1752_ == 0)
{
lean_object* v_snd_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1761_; 
v_snd_1753_ = lean_ctor_get(v_b_1744_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_b_1744_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_b_1744_, 0);
lean_dec(v_unused_1762_);
v___x_1755_ = v_b_1744_;
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_snd_1753_);
lean_dec(v_b_1744_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = lean_box(v___x_1740_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_snd_1753_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
v___y_1746_ = v___x_1759_;
goto v___jp_1745_;
}
}
}
else
{
lean_object* v_snd_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1773_; 
v_snd_1763_ = lean_ctor_get(v_b_1744_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_b_1744_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v_b_1744_, 0);
lean_dec(v_unused_1774_);
v___x_1765_ = v_b_1744_;
v_isShared_1766_ = v_isSharedCheck_1773_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snd_1763_);
lean_dec(v_b_1744_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1773_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1767_ = lean_array_uget_borrowed(v_as_1741_, v_i_1742_);
lean_inc(v___x_1767_);
v___x_1768_ = lean_array_push(v_snd_1763_, v___x_1767_);
v___x_1769_ = lean_box(v___x_1750_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1768_);
lean_ctor_set(v___x_1765_, 0, v___x_1769_);
v___x_1771_ = v___x_1765_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1768_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
v___y_1746_ = v___x_1771_;
goto v___jp_1745_;
}
}
}
}
else
{
return v_b_1744_;
}
v___jp_1745_:
{
size_t v___x_1747_; size_t v___x_1748_; 
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_add(v_i_1742_, v___x_1747_);
v_i_1742_ = v___x_1748_;
v_b_1744_ = v___y_1746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object* v___x_1775_, lean_object* v_as_1776_, lean_object* v_i_1777_, lean_object* v_stop_1778_, lean_object* v_b_1779_){
_start:
{
uint8_t v___x_7129__boxed_1780_; size_t v_i_boxed_1781_; size_t v_stop_boxed_1782_; lean_object* v_res_1783_; 
v___x_7129__boxed_1780_ = lean_unbox(v___x_1775_);
v_i_boxed_1781_ = lean_unbox_usize(v_i_1777_);
lean_dec(v_i_1777_);
v_stop_boxed_1782_ = lean_unbox_usize(v_stop_1778_);
lean_dec(v_stop_1778_);
v_res_1783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_7129__boxed_1780_, v_as_1776_, v_i_boxed_1781_, v_stop_boxed_1782_, v_b_1779_);
lean_dec_ref(v_as_1776_);
return v_res_1783_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2));
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6));
v___x_1799_ = l_Lean_stringToMessageData(v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object* v_elabVal_1802_, lean_object* v_as_1803_, size_t v_i_1804_, size_t v_stop_1805_, lean_object* v_b_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_a_1811_; lean_object* v___y_1816_; uint8_t v___x_1818_; 
v___x_1818_ = lean_usize_dec_eq(v_i_1804_, v_stop_1805_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1));
v___x_1820_ = lean_array_uget_borrowed(v_as_1803_, v_i_1804_);
lean_inc(v___x_1820_);
v___x_1821_ = l_Lean_Syntax_isOfKind(v___x_1820_, v___x_1819_);
if (v___x_1821_ == 0)
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_dec_ref(v_b_1806_);
v___x_1822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3);
v___x_1823_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1820_, v___x_1822_, v___y_1807_, v___y_1808_);
v___y_1816_ = v___x_1823_;
goto v___jp_1815_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1824_);
v___x_1826_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5));
lean_inc(v___x_1825_);
v___x_1827_ = l_Lean_Syntax_isOfKind(v___x_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec_ref(v_b_1806_);
v___x_1828_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1829_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1825_, v___x_1828_, v___y_1807_, v___y_1808_);
lean_dec(v___x_1825_);
v___y_1816_ = v___x_1829_;
goto v___jp_1815_;
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v_v_1832_; lean_object* v___y_1834_; lean_object* v_fst_1835_; lean_object* v_snd_1836_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1882_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1831_ = lean_unsigned_to_nat(2u);
v_v_1832_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1831_);
v___x_1903_ = l_Lean_Syntax_getArg(v___x_1825_, v___x_1824_);
v___x_1904_ = l_Lean_Syntax_getArgs(v___x_1903_);
lean_dec(v___x_1903_);
v___x_1905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8));
v___x_1906_ = lean_array_get_size(v___x_1904_);
v___x_1907_ = lean_nat_dec_lt(v___x_1824_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_dec_ref(v___x_1904_);
v___y_1882_ = v___x_1905_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; lean_object* v_snd_1913_; 
v___x_1908_ = lean_box(v___x_1907_);
v___x_1909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
lean_ctor_set(v___x_1909_, 1, v___x_1905_);
v___x_1910_ = ((size_t)0ULL);
v___x_1911_ = lean_usize_of_nat(v___x_1906_);
v___x_1912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1827_, v___x_1904_, v___x_1910_, v___x_1911_, v___x_1909_);
lean_dec_ref(v___x_1904_);
v_snd_1913_ = lean_ctor_get(v___x_1912_, 1);
lean_inc(v_snd_1913_);
lean_dec_ref(v___x_1912_);
v___y_1882_ = v_snd_1913_;
goto v___jp_1881_;
}
v___jp_1833_:
{
lean_object* v___x_1837_; 
lean_inc(v___y_1834_);
v___x_1837_ = l_Lake_Toml_elabSimpleKey(v___y_1834_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1837_, 1);
v___x_1839_ = l_Lean_Name_str___override(v_fst_1835_, v_a_1838_);
lean_inc_ref(v_snd_1836_);
lean_inc(v___x_1839_);
v___x_1840_ = l_Lake_Toml_RBDict_contains___redArg(v___x_1830_, v___x_1839_, v_snd_1836_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
lean_dec(v___y_1834_);
lean_inc_ref(v_elabVal_1802_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
v___x_1841_ = lean_apply_4(v_elabVal_1802_, v_v_1832_, v___y_1807_, v___y_1808_, lean_box(0));
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_a_1842_);
v___x_1844_ = l_Lake_Toml_RBDict_push___redArg(v___x_1830_, v___x_1839_, v___x_1843_, v_snd_1836_);
v_a_1811_ = v___x_1844_;
goto v___jp_1810_;
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec(v___x_1839_);
lean_dec_ref(v_snd_1836_);
lean_dec_ref(v_elabVal_1802_);
v_a_1845_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1841_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1841_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_dec_ref(v_snd_1836_);
lean_dec(v_v_1832_);
v___x_1853_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
v___x_1854_ = l_Lean_MessageData_ofName(v___x_1839_);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___y_1834_, v___x_1857_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1834_);
v___y_1816_ = v___x_1858_;
goto v___jp_1815_;
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v_snd_1836_);
lean_dec(v_fst_1835_);
lean_dec(v___y_1834_);
lean_dec(v_v_1832_);
lean_dec_ref(v_elabVal_1802_);
v_a_1859_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1837_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1837_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
v___jp_1867_:
{
if (lean_obj_tag(v___y_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v_fst_1871_; lean_object* v_snd_1872_; 
v_a_1870_ = lean_ctor_get(v___y_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___y_1869_, 1);
v_fst_1871_ = lean_ctor_get(v_a_1870_, 0);
lean_inc(v_fst_1871_);
v_snd_1872_ = lean_ctor_get(v_a_1870_, 1);
lean_inc(v_snd_1872_);
lean_dec(v_a_1870_);
v___y_1834_ = v___y_1868_;
v_fst_1835_ = v_fst_1871_;
v_snd_1836_ = v_snd_1872_;
goto v___jp_1833_;
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec(v___y_1868_);
lean_dec(v_v_1832_);
lean_dec_ref(v_elabVal_1802_);
v_a_1873_ = lean_ctor_get(v___y_1869_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___y_1869_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___y_1869_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___y_1869_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
v___jp_1881_:
{
size_t v_sz_1883_; size_t v___x_1884_; lean_object* v___x_1885_; 
v_sz_1883_ = lean_array_size(v___y_1882_);
v___x_1884_ = ((size_t)0ULL);
v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_sz_1883_, v___x_1884_, v___y_1882_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec(v_v_1832_);
lean_dec_ref(v_b_1806_);
v___x_1886_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1887_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1825_, v___x_1886_, v___y_1807_, v___y_1808_);
lean_dec(v___x_1825_);
v___y_1816_ = v___x_1887_;
goto v___jp_1815_;
}
else
{
lean_object* v_val_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v_tailKey_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
lean_dec(v___x_1825_);
v_val_1888_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_val_1888_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_array_get_size(v_val_1888_);
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = lean_nat_sub(v___x_1890_, v___x_1891_);
v_tailKey_1893_ = lean_array_get(v___x_1889_, v_val_1888_, v___x_1892_);
lean_dec(v___x_1892_);
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_array_pop(v_val_1888_);
v___x_1896_ = lean_array_get_size(v___x_1895_);
v___x_1897_ = lean_nat_dec_lt(v___x_1824_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_dec_ref(v___x_1895_);
v___y_1834_ = v_tailKey_1893_;
v_fst_1835_ = v___x_1894_;
v_snd_1836_ = v_b_1806_;
goto v___jp_1833_;
}
else
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_nat_dec_le(v___x_1896_, v___x_1896_);
if (v___x_1898_ == 0)
{
if (v___x_1897_ == 0)
{
lean_dec_ref(v___x_1895_);
v___y_1834_ = v_tailKey_1893_;
v_fst_1835_ = v___x_1894_;
v_snd_1836_ = v_b_1806_;
goto v___jp_1833_;
}
else
{
size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_usize_of_nat(v___x_1896_);
lean_inc_ref(v_b_1806_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1806_, v___x_1827_, v___x_1895_, v___x_1884_, v___x_1899_, v___x_1894_, v_b_1806_, v___y_1807_, v___y_1808_);
lean_dec_ref(v___x_1895_);
v___y_1868_ = v_tailKey_1893_;
v___y_1869_ = v___x_1900_;
goto v___jp_1867_;
}
}
else
{
size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_usize_of_nat(v___x_1896_);
lean_inc_ref(v_b_1806_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1806_, v___x_1827_, v___x_1895_, v___x_1884_, v___x_1901_, v___x_1894_, v_b_1806_, v___y_1807_, v___y_1808_);
lean_dec_ref(v___x_1895_);
v___y_1868_ = v_tailKey_1893_;
v___y_1869_ = v___x_1902_;
goto v___jp_1867_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1914_; 
lean_dec_ref(v_elabVal_1802_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_b_1806_);
return v___x_1914_;
}
v___jp_1810_:
{
size_t v___x_1812_; size_t v___x_1813_; 
v___x_1812_ = ((size_t)1ULL);
v___x_1813_ = lean_usize_add(v_i_1804_, v___x_1812_);
v_i_1804_ = v___x_1813_;
v_b_1806_ = v_a_1811_;
goto _start;
}
v___jp_1815_:
{
if (lean_obj_tag(v___y_1816_) == 0)
{
lean_object* v_a_1817_; 
v_a_1817_ = lean_ctor_get(v___y_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___y_1816_, 1);
v_a_1811_ = v_a_1817_;
goto v___jp_1810_;
}
else
{
lean_dec_ref(v_elabVal_1802_);
return v___y_1816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object* v_elabVal_1915_, lean_object* v_as_1916_, lean_object* v_i_1917_, lean_object* v_stop_1918_, lean_object* v_b_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
size_t v_i_boxed_1923_; size_t v_stop_boxed_1924_; lean_object* v_res_1925_; 
v_i_boxed_1923_ = lean_unbox_usize(v_i_1917_);
lean_dec(v_i_1917_);
v_stop_boxed_1924_ = lean_unbox_usize(v_stop_1918_);
lean_dec(v_stop_1918_);
v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1915_, v_as_1916_, v_i_boxed_1923_, v_stop_boxed_1924_, v_b_1919_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec_ref(v_as_1916_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object* v_as_1926_, size_t v_i_1927_, size_t v_stop_1928_, lean_object* v_b_1929_){
_start:
{
lean_object* v___y_1931_; uint8_t v___x_1935_; 
v___x_1935_ = lean_usize_dec_eq(v_i_1927_, v_stop_1928_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v_snd_1937_; 
v___x_1936_ = lean_array_uget_borrowed(v_as_1926_, v_i_1927_);
v_snd_1937_ = lean_ctor_get(v___x_1936_, 1);
if (lean_obj_tag(v_snd_1937_) == 1)
{
lean_object* v_fst_1938_; lean_object* v_val_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_fst_1938_ = lean_ctor_get(v___x_1936_, 0);
v_val_1939_ = lean_ctor_get(v_snd_1937_, 0);
v___x_1940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
lean_inc(v_val_1939_);
lean_inc(v_fst_1938_);
v___x_1941_ = l_Lake_Toml_RBDict_push___redArg(v___x_1940_, v_fst_1938_, v_val_1939_, v_b_1929_);
v___y_1931_ = v___x_1941_;
goto v___jp_1930_;
}
else
{
v___y_1931_ = v_b_1929_;
goto v___jp_1930_;
}
}
else
{
return v_b_1929_;
}
v___jp_1930_:
{
size_t v___x_1932_; size_t v___x_1933_; 
v___x_1932_ = ((size_t)1ULL);
v___x_1933_ = lean_usize_add(v_i_1927_, v___x_1932_);
v_i_1927_ = v___x_1933_;
v_b_1929_ = v___y_1931_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object* v_as_1942_, lean_object* v_i_1943_, lean_object* v_stop_1944_, lean_object* v_b_1945_){
_start:
{
size_t v_i_boxed_1946_; size_t v_stop_boxed_1947_; lean_object* v_res_1948_; 
v_i_boxed_1946_ = lean_unbox_usize(v_i_1943_);
lean_dec(v_i_1943_);
v_stop_boxed_1947_ = lean_unbox_usize(v_stop_1944_);
lean_dec(v_stop_1944_);
v_res_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_as_1942_, v_i_boxed_1946_, v_stop_boxed_1947_, v_b_1945_);
lean_dec_ref(v_as_1942_);
return v_res_1948_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2));
v___x_1956_ = l_Lean_stringToMessageData(v___x_1955_);
return v___x_1956_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4(void){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object* v_x_1958_, lean_object* v_elabVal_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_1958_);
v___x_1964_ = l_Lean_Syntax_isOfKind(v_x_1958_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec_ref(v_elabVal_1959_);
v___x_1965_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3);
v___x_1966_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1958_, v___x_1965_, v_a_1960_, v_a_1961_);
lean_dec(v_x_1958_);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; lean_object* v_a_1969_; lean_object* v___y_1980_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v_kvs_1992_; lean_object* v_t_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1967_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_unsigned_to_nat(1u);
v___x_1991_ = l_Lean_Syntax_getArg(v_x_1958_, v___x_1990_);
lean_dec(v_x_1958_);
v_kvs_1992_ = l_Lean_Syntax_getArgs(v___x_1991_);
lean_dec(v___x_1991_);
v_t_1993_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
v___x_1994_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_kvs_1992_);
lean_dec_ref(v_kvs_1992_);
v___x_1995_ = lean_array_get_size(v___x_1994_);
v___x_1996_ = lean_nat_dec_lt(v___x_1967_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v___x_1994_);
lean_dec_ref(v_elabVal_1959_);
v_a_1969_ = v_t_1993_;
goto v___jp_1968_;
}
else
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_nat_dec_le(v___x_1995_, v___x_1995_);
if (v___x_1997_ == 0)
{
if (v___x_1996_ == 0)
{
lean_dec_ref(v___x_1994_);
lean_dec_ref(v_elabVal_1959_);
v_a_1969_ = v_t_1993_;
goto v___jp_1968_;
}
else
{
size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = ((size_t)0ULL);
v___x_1999_ = lean_usize_of_nat(v___x_1995_);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1959_, v___x_1994_, v___x_1998_, v___x_1999_, v_t_1993_, v_a_1960_, v_a_1961_);
lean_dec_ref(v___x_1994_);
v___y_1980_ = v___x_2000_;
goto v___jp_1979_;
}
}
else
{
size_t v___x_2001_; size_t v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = lean_usize_of_nat(v___x_1995_);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1959_, v___x_1994_, v___x_2001_, v___x_2002_, v_t_1993_, v_a_1960_, v_a_1961_);
lean_dec_ref(v___x_1994_);
v___y_1980_ = v___x_2003_;
goto v___jp_1979_;
}
}
v___jp_1968_:
{
lean_object* v_items_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v_items_1970_ = lean_ctor_get(v_a_1969_, 0);
lean_inc_ref(v_items_1970_);
lean_dec_ref(v_a_1969_);
v___x_1971_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
v___x_1972_ = lean_array_get_size(v_items_1970_);
v___x_1973_ = lean_nat_dec_lt(v___x_1967_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref(v_items_1970_);
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1971_);
return v___x_1974_;
}
else
{
size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = lean_usize_of_nat(v___x_1972_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_1970_, v___x_1975_, v___x_1976_, v___x_1971_);
lean_dec_ref(v_items_1970_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
return v___x_1978_;
}
}
v___jp_1979_:
{
if (lean_obj_tag(v___y_1980_) == 0)
{
lean_object* v_a_1981_; 
v_a_1981_ = lean_ctor_get(v___y_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___y_1980_, 1);
v_a_1969_ = v_a_1981_;
goto v___jp_1968_;
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
v_a_1982_ = lean_ctor_get(v___y_1980_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___y_1980_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___y_1980_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___y_1980_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object* v_x_2004_, lean_object* v_elabVal_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2004_, v_elabVal_2005_, v_a_2006_, v_a_2007_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(lean_object* v_00_u03b1_2010_, lean_object* v_ref_2011_, lean_object* v_msg_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v_ref_2011_, v_msg_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object* v_00_u03b1_2018_, lean_object* v_ref_2019_, lean_object* v_msg_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_00_u03b1_2018_, v_ref_2019_, v_msg_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v___y_2021_);
lean_dec(v_ref_2019_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(lean_object* v_00_u03b1_2026_, lean_object* v_msg_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_2027_, v___y_2029_, v___y_2030_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2033_, lean_object* v_msg_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(v_00_u03b1_2033_, v_msg_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2039_;
}
}
static lean_object* _init_l_Lake_Toml_elabVal___closed__1(void){
_start:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = ((lean_object*)(l_Lake_Toml_elabVal___closed__0));
v___x_2042_ = l_Lean_stringToMessageData(v___x_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object* v_x_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lake_Toml_elabVal(v_x_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object* v_x_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
lean_inc(v_x_2048_);
v___x_2053_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___x_2054_; uint8_t v___x_2055_; 
v___x_2054_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
lean_inc(v_x_2048_);
v___x_2055_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2054_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
lean_inc(v_x_2048_);
v___x_2057_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
lean_inc(v_x_2048_);
v___x_2059_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
lean_inc(v_x_2048_);
v___x_2061_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
lean_inc(v_x_2048_);
v___x_2063_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_2048_);
v___x_2065_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_2048_);
v___x_2067_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_2048_);
v___x_2069_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2048_);
v___x_2071_ = l_Lean_Syntax_isOfKind(v_x_2048_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_obj_once(&l_Lake_Toml_elabVal___closed__1, &l_Lake_Toml_elabVal___closed__1_once, _init_l_Lake_Toml_elabVal___closed__1);
v___x_2073_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2048_, v___x_2072_, v_a_2049_, v_a_2050_);
lean_dec(v_x_2048_);
return v___x_2073_;
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2048_);
v___x_2075_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2048_, v___x_2074_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2084_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2080_, 0, v_x_2048_);
lean_ctor_set(v___x_2080_, 1, v_a_2076_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_x_2048_);
v_a_2085_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2075_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2075_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2048_);
v___x_2094_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_2048_, v___x_2093_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2099_, 0, v_x_2048_);
lean_ctor_set(v___x_2099_, 1, v_a_2095_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_x_2048_);
v_a_2104_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2094_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2094_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
else
{
lean_object* v___x_2112_; 
lean_inc(v_x_2048_);
v___x_2112_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2122_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2122_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2122_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; uint8_t v___x_2118_; lean_object* v___x_2120_; 
v___x_2117_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_2117_, 0, v_x_2048_);
v___x_2118_ = lean_unbox(v_a_2113_);
lean_dec(v_a_2113_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*1, v___x_2118_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2117_);
v___x_2120_ = v___x_2115_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2117_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v_x_2048_);
v_a_2123_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2112_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2112_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
else
{
lean_object* v___x_2131_; 
lean_inc(v_x_2048_);
v___x_2131_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2140_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2134_ = v___x_2131_;
v_isShared_2135_ = v_isSharedCheck_2140_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2131_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2140_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2136_, 0, v_x_2048_);
lean_ctor_set(v___x_2136_, 1, v_a_2132_);
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2136_);
v___x_2138_ = v___x_2134_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec(v_x_2048_);
v_a_2141_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2131_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2131_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
else
{
lean_object* v___x_2149_; 
v___x_2149_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2158_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_x_2048_);
lean_ctor_set(v___x_2154_, 1, v_a_2150_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2154_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec(v_x_2048_);
v_a_2159_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2149_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2149_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
else
{
lean_object* v___x_2167_; 
v___x_2167_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2177_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2177_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2177_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2172_ = lean_nat_to_int(v_a_2168_);
v___x_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2173_, 0, v_x_2048_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2173_);
v___x_2175_ = v___x_2170_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_x_2048_);
v_a_2178_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2167_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2167_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
else
{
lean_object* v___x_2186_; 
v___x_2186_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2196_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2189_ = v___x_2186_;
v_isShared_2190_ = v_isSharedCheck_2196_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2186_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2196_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2191_ = lean_nat_to_int(v_a_2187_);
v___x_2192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_x_2048_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 0, v___x_2192_);
v___x_2194_ = v___x_2189_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2192_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_x_2048_);
v_a_2197_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2186_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2186_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
else
{
lean_object* v___x_2205_; 
v___x_2205_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2215_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2210_ = lean_nat_to_int(v_a_2206_);
v___x_2211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2211_, 0, v_x_2048_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_x_2048_);
v_a_2216_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2205_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2205_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2229_, 0, v_x_2048_);
lean_ctor_set(v___x_2229_, 1, v_a_2225_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec(v_x_2048_);
v_a_2234_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2224_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2224_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
else
{
lean_object* v___x_2242_; 
v___x_2242_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_2048_, v_a_2049_, v_a_2050_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2252_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2252_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; double v___x_2248_; lean_object* v___x_2250_; 
v___x_2247_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_2247_, 0, v_x_2048_);
v___x_2248_ = lean_unbox_float(v_a_2243_);
lean_dec(v_a_2243_);
lean_ctor_set_float(v___x_2247_, sizeof(void*)*1, v___x_2248_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2247_);
v___x_2250_ = v___x_2245_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2247_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
else
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2260_; 
lean_dec(v_x_2048_);
v_a_2253_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2255_ = v___x_2242_;
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2242_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2260_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2258_; 
if (v_isShared_2256_ == 0)
{
v___x_2258_ = v___x_2255_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2253_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
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
