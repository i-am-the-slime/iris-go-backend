export const nullable = (value) => (whenNull) => (whenPresent) => (value == null ? whenNull : whenPresent(value));
