
#module_parameters(COMPILE_TIME_BAKE: bool = false);

Dehydrated :: struct (T: Type) {
    memory: *void;
    data: T;
}

serializer_hydrate :: (dehydrated: Dehydrated($T)) -> T {
    info :: type_info(T);

    hydrated: T;
    memcpy(*hydrated, *dehydrated.data, info.runtime_size);
    serializer_hydrate(*hydrated, info);

    return hydrated;
}

serializer_read :: ($T: Type, data: [] u8, validate_modtime: bool = false) -> bool, Dehydrated(T) {
    info :: type_info(T);
    #run validate_generic(info);

    assert(data.count >= info.runtime_size, "Not enough serialization data for reading. %\n", T);

    value: Dehydrated(T);
    value.memory = data.data;
    memcpy(*value.data, data.data, info.runtime_size);

    serializer_read_generic(*value.data, data, info);

    return true, value;
}

serializer_write :: (data: $T) -> [] u8 {
    info :: type_info(T);
    #run validate_generic(info);

    output_size := serializer_get_size(*data, info);

    output := NewArray(output_size, u8);
    index, written := write_data(output, 0, *data, info.runtime_size);

    index = serializer_write_generic(output, index, written, info);
    assert(index == output_size, "Serializer wrote unexpected number of bytes. % % %\n", T, index, output_size);

    return output;
}

serializer_get_size :: (data: $T) -> int {
    info :: type_info(T);
    return serializer_get_size(*data, info);
}

serializer_get_size :: (data: *void, info: *Type_Info) -> int {
    return info.runtime_size + serializer_write_generic(.[], 0, data, info);
}

is_pod :: ($T: Type) -> bool {
    info :: type_info(T);
    return is_pod(info);
}

is_pod :: (info: *Type_Info) -> bool {
    if info.type == {
        case .INTEGER;
            return true;
        case .FLOAT;
            return true;
        case .BOOL;
            return true;
        case .STRING;
            return false;
        case .POINTER;
            return false;
        case .STRUCT;
            struct_info := cast(*Type_Info_Struct) info;
            for member: struct_info.members {
                if member.flags & .CONSTANT {
                    continue;
                }
                if !is_pod(member.type) {
                    return false;
                }
            }
            return true;
        case .ARRAY;
            array_info := cast(*Type_Info_Array) info;
            if array_info.array_type == .FIXED {
                return is_pod(array_info.element_type);
            }
            return false;
        case .ENUM;
            return true;
        case .VARIANT;
            variant_info := cast(*Type_Info_Variant) info;
            return is_pod(variant_info.variant_of);
        case .PROCEDURE;
            return false;
        case;
            assert(false, "Unsupported is_pod type. % %\nMaybe you need to @serializer_skip this?\n", info.type, (cast(*Type) *info).*);
            return false;
    }
}

#scope_file

serializer_hydrate_initialize :: (output: *void, info: *Type_Info) {
    if info.type == .STRUCT && (cast(*Type_Info_Struct) info).initializer {
        (cast(*Type_Info_Struct) info).initializer(output);
    } else {
        memset(output, 0, info.runtime_size);
    }
}

serializer_hydrate :: (output: *void, info: *Type_Info) {
    if is_pod(info) {
        return;
    }

    if info.type == {
        case .STRING;
            output_string := cast(*string) output;
            output_string.* = copy_string(output_string.*);

        case .POINTER;
            pointer_info := cast(*Type_Info_Pointer) info;

            output_pointer := cast(**void) output;

            if output_pointer.* {
                allocated := alloc(pointer_info.pointer_to.runtime_size);
                memcpy(allocated, output_pointer.*, pointer_info.pointer_to.runtime_size);
                output_pointer.* = allocated;

                serializer_hydrate(output_pointer.*, pointer_info.pointer_to);
            }

        case .STRUCT;
            struct_info := cast(*Type_Info_Struct) info;

            struct_type := (cast(*Type) *info).*;
            if struct_type == Allocator {
                allocator := cast(*Allocator) output;
                allocator.* = context.allocator;
                return;
            }

            for member: struct_info.members {
                if member.flags & .CONSTANT {
                    continue;
                }

                if is_pod(member.type) {
                    continue;
                }

                if array_find(member.notes, "serializer_skip") {
                    serializer_hydrate_initialize(output + member.offset_in_bytes, member.type);
                    continue;
                }

                serializer_hydrate(output + member.offset_in_bytes, member.type);
            }

        case .ARRAY;
            array_info := cast(*Type_Info_Array) info;

            if #complete array_info.array_type == {
                case .FIXED;
                    assert(!is_pod(array_info.element_type), "Hydrating a fixed array that's pod. This should never happen.\n");
                    for i: 0..array_info.array_count - 1 {
                        output_member := output + i * array_info.element_type.runtime_size;
                        serializer_hydrate(output_member, array_info.element_type);
                    }

                case .VIEW;
                    output_array := cast(*Array_View_64) output;

                    allocated := alloc(output_array.count * array_info.element_type.runtime_size);
                    memcpy(allocated, output_array.data, output_array.count * array_info.element_type.runtime_size);
                    output_array.data = allocated;

                    if !is_pod(array_info.element_type) {
                        for i: 0..output_array.count - 1 {
                            output_member := output_array.data + i * array_info.element_type.runtime_size;
                            serializer_hydrate(output_member, array_info.element_type);
                        }
                    }

                case .RESIZABLE;
                    output_array := cast(*Resizable_Array) output;

                    allocated := alloc(output_array.count * array_info.element_type.runtime_size);
                    memcpy(allocated, output_array.data, output_array.count * array_info.element_type.runtime_size);
                    output_array.data = allocated;
                    output_array.allocated = output_array.count;
                    output_array.allocator = context.allocator;

                    if !is_pod(array_info.element_type) {
                        for i: 0..output_array.count - 1 {
                            output_member := output_array.data + i * array_info.element_type.runtime_size;
                            serializer_hydrate(output_member, array_info.element_type);
                        }
                    }
            }

        case .VARIANT;
            variant_info := cast(*Type_Info_Variant) info;
            serializer_hydrate(output, variant_info.variant_of);

        case;
            assert(false, "Unsupported non-pod hydrate type. %\n", info.type);
    }
}

serializer_write_generic :: (output: [] u8, index: int, data: *void, info: *Type_Info) -> int {
    if is_pod(info) {
        return index;
    }

    if info.type == {
        case .STRING;
            index = serializer_write_string(output, index, data, cast(*Type_Info_String) info);
        case .POINTER;
            index = serializer_write_pointer(output, index, data, cast(*Type_Info_Pointer) info);
        case .STRUCT;
            index = serializer_write_struct(output, index, data, cast(*Type_Info_Struct) info);
        case .ARRAY;
            index = serializer_write_array(output, index, data, cast(*Type_Info_Array) info);
        case .VARIANT;
            variant_info := cast(*Type_Info_Variant) info;
            index = serializer_write_generic(output, index, data, variant_info.variant_of);
        case;
            assert(false, "Unsupported non-pod write type. %\n", info.type);
    }

    return index;
}

serializer_write_string :: (output: [] u8, index: int, data: *void, info: *Type_Info_String) -> int {
    string_value := cast(*string) data;

    if string_value.data {
        string_pointer := string_value.data;
        if output {
            string_value.data = cast(*void) index;
        }

        index = write_data(output, index, string_pointer, string_value.count);
    }

    return index;
}

serializer_write_pointer :: (output: [] u8, index: int, data: *void, info: *Type_Info_Pointer) -> int {
    pointer_value := cast(**void) data;

    if pointer_value.* {
        pointer_pointer := pointer_value.*;
        if output {
            pointer_value.* = cast(*void) index;
        }

        written: *void;
        index, written = write_data(output, index, pointer_pointer, info.pointer_to.runtime_size);

        index = serializer_write_generic(output, index, written, info.pointer_to);
    }

    return index;
}

serializer_write_struct :: (output: [] u8, index: int, data: *void, info: *Type_Info_Struct) -> int {
    struct_type := (cast(*Type) *info).*;
    if struct_type == Allocator {
        return index;
    }

    for member: info.members {
        if member.flags & .CONSTANT {
            continue;
        }

        if is_pod(member.type) {
            continue;
        }

        if array_find(member.notes, "serializer_skip") {
            continue;
        }

        member_data := data + member.offset_in_bytes;
        index = serializer_write_generic(output, index, member_data, member.type);
    }

    return index;
}

serializer_write_array :: (output: [] u8, index: int, data: *void, info: *Type_Info_Array) -> int {
    if #complete info.array_type == {
        case .FIXED;
            // if you're writing a fixed entry then it is not pod
            // otherwise we wouldn't be here
            assert(!is_pod(info.element_type), "Writing a fixed array that's pod. This should never happen.\n");

            for i: 0..info.array_count - 1 {
                member_data := data + i * info.element_type.runtime_size;
                index = serializer_write_generic(output, index, member_data, info.element_type);
            }

        case .VIEW;
            array_value := cast(*Array_View_64) data;
            if array_value.data {
                array_pointer := array_value.data;
                if output {
                    array_value.data = cast(*void) index;
                }

                written: *void;
                index, written = write_data(output, index, array_pointer, array_value.count * info.element_type.runtime_size);

                if !is_pod(info.element_type) {
                    for i: 0..array_value.count - 1 {
                        member_data := written + i * info.element_type.runtime_size;
                        index = serializer_write_generic(output, index, member_data, info.element_type);
                    }
                }
            }

        case .RESIZABLE;
            array_value := cast(*Resizable_Array) data;
            if array_value.data {
                array_pointer := array_value.data;
                if output {
                    array_value.data = cast(*void) index;
                }

                written: *void;
                index, written = write_data(output, index, array_pointer, array_value.count * info.element_type.runtime_size);

                if !is_pod(info.element_type) {
                    for i: 0..array_value.count - 1 {
                        member_data := written + i * info.element_type.runtime_size;
                        index = serializer_write_generic(output, index, member_data, info.element_type);
                    }
                }

                array_value.allocator = assert_allocator;
            }
    }

    return index;
}

write_data :: (output: [] u8, index: int, data: *void, size: int) -> int, *void {
    if output.count {
        assert(output.count - index >= size, "Not enough space to write serializer data.\n");
        memcpy(output.data + index, data, size);
        return index + size, output.data + index;
    }

    return index + size, data;
}

serializer_read_generic :: (value: *void, data: [] u8, info: *Type_Info) {
    if is_pod(info) {
        return;
    }

    if info.type == {
        case .STRING;
            serializer_read_string(value, data, cast(*Type_Info_String) info);
        case .POINTER;
            serializer_read_pointer(value, data, cast(*Type_Info_Pointer) info);
        case .STRUCT;
            serializer_read_struct(value, data, cast(*Type_Info_Struct) info);
        case .ARRAY;
            serializer_read_array(value, data, cast(*Type_Info_Array) info);
        case .VARIANT;
            variant_info := cast(*Type_Info_Variant) info;
            serializer_read_generic(value, data, variant_info.variant_of);
        case;
            assert(false, "Unsupported non-pod read type. %\n", info.type);
    }
}

serializer_read_string :: (value: *void, data: [] u8, info: *Type_Info_String) {
    string_value := cast(*string) value;

    if string_value.data {
        string_value.data += cast(int) data.data;
    }
}

serializer_read_pointer :: (value: *void, data: [] u8, info: *Type_Info_Pointer) {
    pointer_value := cast(**void) value;

    if pointer_value.* {
        pointer_value.* += cast(int) data.data;

        serializer_read_generic(pointer_value.*, data, info.pointer_to);
    }
}

serializer_read_struct :: (value: *void, data: [] u8, info: *Type_Info_Struct) {
    struct_type := (cast(*Type) *info).*;
    if struct_type == Allocator {
        allocator := cast(*Allocator) value;
        allocator.* = assert_allocator;
        return;
    }

    for member: info.members {
        if member.flags & .CONSTANT {
            continue;
        }

        if is_pod(member.type) {
            continue;
        }

        if array_find(member.notes, "serializer_skip") {
            continue;
        }

        member_value := value + member.offset_in_bytes;
        serializer_read_generic(member_value, data, member.type);
    }
}

serializer_read_array :: (value: *void, data: [] u8, info: *Type_Info_Array) {
    if #complete info.array_type == {
        case .FIXED;
            // if you're reading a fixed entry then it is not pod
            // otherwise we wouldn't be here
            assert(!is_pod(info.element_type), "Reading a fixed array that's pod. This should never happen.\n");

            for i: 0..info.array_count - 1 {
                member_value := value + i * info.element_type.runtime_size;
                serializer_read_generic(member_value, data, info.element_type);
            }

        case .VIEW;
            array_value := cast(*Array_View_64) value;
            if array_value.data {
                array_value.data += cast(int) data.data;

                if !is_pod(info.element_type) {
                    for i: 0..array_value.count - 1 {
                        member_value := array_value.data + i * info.element_type.runtime_size;
                        serializer_read_generic(member_value, data, info.element_type);
                    }
                }
            }

        case .RESIZABLE;
            array_value := cast(*Resizable_Array) value;
            if array_value.data {
                array_value.data += cast(int) data.data;

                if !is_pod(info.element_type) {
                    for i: 0..array_value.count - 1 {
                        member_value := array_value.data + i * info.element_type.runtime_size;
                        serializer_read_generic(member_value, data, info.element_type);
                    }
                }

                array_value.allocator = assert_allocator;
            }
    }
}

#scope_file

Validated :: struct {
    info: *Type_Info;
    parent: *Validated;
}

has_parent :: (validated: *Validated, parent: *Type_Info) -> bool {
    if validated.info == parent {
        return true;
    }
    return validated.parent && has_parent(validated.parent, parent);
}

validate_generic :: (info: *Type_Info, validated_parent: *Validated = null) -> bool {
    if validated_parent && has_parent(validated_parent, info) {
        return true;
    }

    validated_child: Validated;
    validated_child.info = info;
    validated_child.parent = validated_parent;

    if info.type == {
        case .POINTER;
            return validate_generic((cast(*Type_Info_Pointer) info).pointer_to, *validated_child);

        case .STRUCT;
            return validate_struct(cast(*Type_Info_Struct) info, *validated_child);

        case .ARRAY;
            return validate_generic((cast(*Type_Info_Array) info).element_type, *validated_child);

        case;
            return true;
    }
}

validate_struct :: (info: *Type_Info_Struct, validated_parent: *Validated) -> bool {
    // a struct is valid as long as it has no overlapping non-pod members
    for member_a, index_a: info.members {
        if member_a.flags & .CONSTANT {
            continue;
        }

        if is_pod(member_a.type) {
            continue;
        }

        if array_find(member_a.notes, "serializer_skip") {
            continue;
        }

        range_a := int.[member_a.offset_in_bytes, member_a.offset_in_bytes + member_a.type.runtime_size - 1];

        // since member_a is not pod, we will check for any overlapping member_b values
        for member_b, index_b: info.members {
            if member_b.flags & .CONSTANT {
                continue;
            }

            if index_a == index_b {
                continue;
            }

            range_b := int.[member_b.offset_in_bytes, member_b.offset_in_bytes + member_b.type.runtime_size - 1];

            overlapping := range_a[0] <= range_b[1] && range_a[1] >= range_b[0];
            if overlapping {
                assert(false, "Found overlapping non-pod struct members.\nMaybe @serializer_skip this?\n%\nt\t%\n\t%", info.name, member_a.name, member_b.name);
                return false;
            }
        }

        if !validate_generic(member_a.type, validated_parent) {
            return false;
        }
    }

    return true;
}

assert_allocator_proc :: (mode: Allocator_Mode, size: s64, old_size: s64, old_memory: *void, allocator_data: *void) -> *void {
    assert(false, "You cannot allocate serialized data without first hydrating it.\n");
    return null;
}

assert_allocator :: Allocator.{assert_allocator_proc, null};

#import "Basic";
