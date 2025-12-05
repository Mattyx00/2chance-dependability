package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the Categoria class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - Default constructor behavior
 * - Parameterized constructor with various inputs (null, empty, whitespace,
 * valid)
 * - Getter method behavior
 * - Setter method behavior with state preservation
 */
@DisplayName("Categoria Tests")
class CategoriaTest {

    // ========================================================================
    // Constructor Tests: Categoria()
    // ========================================================================

    @Test
    @DisplayName("Default constructor should create Categoria with null name")
    void shouldCreateCategoriaWithNullNameWhenUsingDefaultConstructor() {
        // Arrange & Act
        Categoria categoria = new Categoria();

        // Assert
        assertNotNull(categoria, "Categoria instance should be created");
        assertNull(categoria.getNomeCategoria(), "Nome categoria should be null before setter call");
    }

    // ========================================================================
    // Constructor Tests: Categoria(String nomeCategoria)
    // ========================================================================

    @Test
    @DisplayName("Parameterized constructor should throw exception when nomeCategoria is null")
    void shouldThrowIllegalArgumentExceptionWhenNomeCategoriaIsNull() {
        // Arrange
        String nomeCategoria = null;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Categoria(nomeCategoria),
                "Should throw IllegalArgumentException for null name");
        assertTrue(exception.getMessage().contains("null o vuoto"),
                "Exception message should mention 'null o vuoto'");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when nomeCategoria is empty")
    void shouldThrowIllegalArgumentExceptionWhenNomeCategoriaIsEmpty() {
        // Arrange
        String nomeCategoria = "";

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Categoria(nomeCategoria),
                "Should throw IllegalArgumentException for empty name");
        assertTrue(exception.getMessage().contains("null o vuoto"),
                "Exception message should mention 'null o vuoto'");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when nomeCategoria is whitespace")
    void shouldThrowIllegalArgumentExceptionWhenNomeCategoriaIsWhitespace() {
        // Arrange
        String nomeCategoria = "   ";

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Categoria(nomeCategoria),
                "Should throw IllegalArgumentException for whitespace-only name");
        assertTrue(exception.getMessage().contains("null o vuoto"),
                "Exception message should mention 'null o vuoto'");
    }

    @Test
    @DisplayName("Parameterized constructor should create Categoria with valid single-character name")
    void shouldCreateCategoriaWithValidSingleCharacterName() {
        // Arrange
        String nomeCategoria = "A";

        // Act
        Categoria categoria = new Categoria(nomeCategoria);

        // Assert
        assertNotNull(categoria, "Categoria instance should be created");
        assertEquals("A", categoria.getNomeCategoria(),
                "Nome categoria should match the input value");
    }

    @Test
    @DisplayName("Parameterized constructor should create Categoria when nomeCategoria is valid")
    void shouldCreateCategoriaWhenNomeCategoriaIsValid() {
        // Arrange
        String nomeCategoria = "Electronics";

        // Act
        Categoria categoria = new Categoria(nomeCategoria);

        // Assert
        assertNotNull(categoria, "Categoria instance should be created");
        assertEquals("Electronics", categoria.getNomeCategoria(),
                "Nome categoria should match the input value");
    }

    @Test
    @DisplayName("Parameterized constructor should create Categoria with very long name")
    void shouldCreateCategoriaWithVeryLongName() {
        // Arrange
        String nomeCategoria = "Very Long Category Name With Many Words And Characters To Test Boundary Conditions";

        // Act
        Categoria categoria = new Categoria(nomeCategoria);

        // Assert
        assertNotNull(categoria, "Categoria instance should be created");
        assertEquals(nomeCategoria, categoria.getNomeCategoria(),
                "Nome categoria should match the long input value");
    }

    // ========================================================================
    // Parameterized Constructor Tests (Combined)
    // ========================================================================

    @ParameterizedTest(name = "[{index}] {0}")
    @CsvSource(value = {
            "valid single char | A | false",
            "valid normal name | Electronics | false",
            "valid long name | Very Long Category Name With Many Words | false",
            "valid with spaces | Home & Garden | false",
            "valid with numbers | Category 123 | false"
    }, delimiter = '|')
    @DisplayName("Parameterized constructor should handle valid names correctly")
    void shouldHandleValidNamesInParameterizedConstructor(String scenario, String inputName, boolean shouldThrow) {
        // Act & Assert
        assertDoesNotThrow(() -> {
            Categoria categoria = new Categoria(inputName);
            assertEquals(inputName, categoria.getNomeCategoria(),
                    "Nome categoria should match input for: " + scenario);
        }, "Should not throw exception for: " + scenario);
    }

    @ParameterizedTest(name = "[{index}] Invalid input: ''{0}''")
    @ValueSource(strings = { "", "   ", "\t", "\n" })
    @DisplayName("Parameterized constructor should throw exception for empty/whitespace names")
    void shouldThrowExceptionForEmptyOrWhitespaceNames(String invalidName) {
        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> new Categoria(invalidName),
                "Should throw exception for invalid name: '" + invalidName + "'");
    }

    // ========================================================================
    // Getter Tests: getNomeCategoria()
    // ========================================================================

    @Test
    @DisplayName("getNomeCategoria should return null when not yet set (default constructor)")
    void shouldReturnNullWhenNomeCategoriaNotYetSet() {
        // Arrange
        Categoria categoria = new Categoria();

        // Act
        String result = categoria.getNomeCategoria();

        // Assert
        assertNull(result, "Should return null for default-constructed Categoria");
    }

    @Test
    @DisplayName("getNomeCategoria should return nome when set via constructor")
    void shouldReturnNomeCategoriaWhenSet() {
        // Arrange
        Categoria categoria = new Categoria("Books");

        // Act
        String result = categoria.getNomeCategoria();

        // Assert
        assertEquals("Books", result, "Should return the nome set via constructor");
    }

    // ========================================================================
    // Setter Tests: setNomeCategoria(String nomeCategoria)
    // ========================================================================

    @Test
    @DisplayName("setNomeCategoria should throw exception when setting null name")
    void shouldThrowIllegalArgumentExceptionWhenSettingNullName() {
        // Arrange
        Categoria categoria = new Categoria("Original");

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> categoria.setNomeCategoria(null),
                "Should throw IllegalArgumentException when setting null");

        // Verify state is unchanged
        assertEquals("Original", categoria.getNomeCategoria(),
                "Nome categoria should remain unchanged after exception");
        assertTrue(exception.getMessage().contains("null o vuoto"),
                "Exception message should mention 'null o vuoto'");
    }

    @Test
    @DisplayName("setNomeCategoria should throw exception when setting empty name")
    void shouldThrowIllegalArgumentExceptionWhenSettingEmptyName() {
        // Arrange
        Categoria categoria = new Categoria("Original");

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> categoria.setNomeCategoria(""),
                "Should throw IllegalArgumentException when setting empty string");

        // Verify state is unchanged
        assertEquals("Original", categoria.getNomeCategoria(),
                "Nome categoria should remain unchanged after exception");
    }

    @Test
    @DisplayName("setNomeCategoria should throw exception when setting whitespace name")
    void shouldThrowIllegalArgumentExceptionWhenSettingWhitespaceName() {
        // Arrange
        Categoria categoria = new Categoria("Original");

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> categoria.setNomeCategoria("   "),
                "Should throw IllegalArgumentException when setting whitespace");

        // Verify state is unchanged
        assertEquals("Original", categoria.getNomeCategoria(),
                "Nome categoria should remain unchanged after exception");
    }

    @Test
    @DisplayName("setNomeCategoria should set valid name on default-constructed object")
    void shouldSetValidNameOnDefaultConstructedObject() {
        // Arrange
        Categoria categoria = new Categoria();

        // Act
        categoria.setNomeCategoria("NewCategory");

        // Assert
        assertEquals("NewCategory", categoria.getNomeCategoria(),
                "Should set nome categoria on default-constructed object");
    }

    @Test
    @DisplayName("setNomeCategoria should replace existing name with new valid name")
    void shouldReplaceExistingNameWithNewValidName() {
        // Arrange
        Categoria categoria = new Categoria("OldCategory");

        // Act
        categoria.setNomeCategoria("NewCategory");

        // Assert
        assertEquals("NewCategory", categoria.getNomeCategoria(),
                "Should replace existing nome with new value");
    }

    @Test
    @DisplayName("setNomeCategoria should handle special characters")
    void shouldSetNameWithSpecialCharacters() {
        // Arrange
        Categoria categoria = new Categoria("Initial");
        String specialName = "Electronics & Gadgets (2024)!";

        // Act
        categoria.setNomeCategoria(specialName);

        // Assert
        assertEquals(specialName, categoria.getNomeCategoria(),
                "Should handle names with special characters");
    }

    @Test
    @DisplayName("setNomeCategoria should handle unicode characters")
    void shouldSetNameWithUnicodeCharacters() {
        // Arrange
        Categoria categoria = new Categoria("Initial");
        String unicodeName = "Électronique et Gadgets 中文";

        // Act
        categoria.setNomeCategoria(unicodeName);

        // Assert
        assertEquals(unicodeName, categoria.getNomeCategoria(),
                "Should handle names with unicode characters");
    }

    // ========================================================================
    // Parameterized Setter Tests
    // ========================================================================

    @ParameterizedTest(name = "[{index}] {0}")
    @CsvSource(value = {
            "set valid on default | null | NewCategory | false",
            "replace valid with valid | OldCategory | NewCategory | false",
            "set single char | Initial | X | false",
            "set long name | Short | Very Long New Category Name | false"
    }, delimiter = '|', nullValues = "null")
    @DisplayName("setNomeCategoria should handle various valid scenarios")
    void shouldHandleValidSetNomeCategoriaScenarios(String scenario, String initialName,
            String newName, boolean shouldThrow) {
        // Arrange
        Categoria categoria = initialName == null ? new Categoria() : new Categoria(initialName);

        // Act & Assert
        assertDoesNotThrow(() -> {
            categoria.setNomeCategoria(newName);
            assertEquals(newName, categoria.getNomeCategoria(),
                    "Nome should be updated for: " + scenario);
        }, "Should not throw exception for: " + scenario);
    }
}
