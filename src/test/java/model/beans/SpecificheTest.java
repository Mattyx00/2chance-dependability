package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the Specifiche class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - Default constructor behavior
 * - Parameterized constructor with valid/invalid nome and valore
 * - Getter methods
 * - Setter methods with null/empty/valid inputs
 */
@DisplayName("Specifiche Tests")
class SpecificheTest {

    // ========================================================================
    // Constructor Tests: Specifiche()
    // ========================================================================

    @Test
    @DisplayName("Default constructor should create Specifiche with null fields")
    void shouldCreateSpecificheWithNullFieldsWhenUsingDefaultConstructor() {
        // Arrange & Act
        Specifiche spec = new Specifiche();

        // Assert
        assertNotNull(spec, "Specifiche instance should be created");
        assertNull(spec.getNome(), "Nome should be null with default constructor");
        assertNull(spec.getValore(), "Valore should be null with default constructor");
    }

    // ========================================================================
    // Constructor Tests: Specifiche(String nome, String valore)
    // ========================================================================

    @Test
    @DisplayName("Parameterized constructor should create Specifiche when both parameters are valid")
    void shouldCreateSpecificheWhenBothParametersAreValid() {
        // Arrange
        String nome = "RAM";
        String valore = "16GB";

        // Act
        Specifiche spec = new Specifiche(nome, valore);

        // Assert
        assertNotNull(spec, "Specifiche instance should be created");
        assertEquals("RAM", spec.getNome(), "Nome should match");
        assertEquals("16GB", spec.getValore(), "Valore should match");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when nome is null")
    void shouldThrowExceptionWhenNomeIsNull() {
        // Arrange
        String nome = null;
        String valore = "16GB";

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Specifiche(nome, valore),
                "Should throw exception for null nome");
        assertTrue(exception.getMessage().contains("nome della specifica non può essere null o vuoto"),
                "Exception message should mention nome");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when valore is null")
    void shouldThrowExceptionWhenValoreIsNull() {
        // Arrange
        String nome = "RAM";
        String valore = null;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Specifiche(nome, valore),
                "Should throw exception for null valore");
        assertTrue(exception.getMessage().contains("valore della specifica non può essere null o vuoto"),
                "Exception message should mention valore");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when nome is empty")
    void shouldThrowExceptionWhenNomeIsEmpty() {
        // Arrange
        String nome = "";
        String valore = "16GB";

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> new Specifiche(nome, valore),
                "Should throw exception for empty nome");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when valore is whitespace")
    void shouldThrowExceptionWhenValoreIsWhitespace() {
        // Arrange
        String nome = "RAM";
        String valore = "   ";

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> new Specifiche(nome, valore),
                "Should throw exception for whitespace valore");
    }

    @Test
    @DisplayName("Parameterized constructor should throw exception when both are null")
    void shouldThrowExceptionWhenBothParametersAreNull() {
        // Arrange
        String nome = null;
        String valore = null;

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Specifiche(nome, valore),
                "Should throw exception when both null");
        // Nome is checked first
        assertTrue(exception.getMessage().contains("nome"),
                "Exception should mention nome (checked first)");
    }

    // ========================================================================
    // Parameterized Constructor Tests
    // ========================================================================

    @ParameterizedTest(name = "[{index}] nome=''{0}'', valore=''{1}''")
    @CsvSource(value = {
            "CPU | Intel i7",
            "RAM | 16GB DDR4",
            "Storage | 512GB SSD",
            "Graphics | NVIDIA RTX 3060",
            "A | B" // Minimal valid case
    }, delimiter = '|')
    @DisplayName("Parameterized constructor should handle valid specification pairs")
    void shouldHandleValidSpecificationPairs(String nome, String valore) {
        // Act & Assert
        assertDoesNotThrow(() -> {
            Specifiche spec = new Specifiche(nome, valore);
            assertEquals(nome, spec.getNome(), "Nome should match");
            assertEquals(valore, spec.getValore(), "Valore should match");
        });
    }

    @ParameterizedTest(name = "[{index}] Invalid nome: ''{0}''")
    @NullAndEmptySource
    @ValueSource(strings = { "   ", "\t", "\n" })
    @DisplayName("Parameterized constructor should throw exception for invalid nome")
    void shouldThrowExceptionForInvalidNome(String invalidNome) {
        // Arrange
        String valore = "ValidValue";

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> new Specifiche(invalidNome, valore),
                "Should throw exception for invalid nome: '" + invalidNome + "'");
    }

    @ParameterizedTest(name = "[{index}] Invalid valore: ''{0}''")
    @NullAndEmptySource
    @ValueSource(strings = { "   ", "\t" })
    @DisplayName("Parameterized constructor should throw exception for invalid valore")
    void shouldThrowExceptionForInvalidValore(String invalidValore) {
        // Arrange
        String nome = "ValidKey";

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> new Specifiche(nome, invalidValore),
                "Should throw exception for invalid valore: '" + invalidValore + "'");
    }

    // ========================================================================
    // Getter Tests: getNome()
    // ========================================================================

    @Test
    @DisplayName("getNome should return null when not set (default constructor)")
    void shouldReturnNullWhenNomeNotSet() {
        // Arrange
        Specifiche spec = new Specifiche();

        // Act
        String result = spec.getNome();

        // Assert
        assertNull(result, "Should return null for default-constructed Specifiche");
    }

    @Test
    @DisplayName("getNome should return nome when set via constructor")
    void shouldReturnNomeWhenSet() {
        // Arrange
        Specifiche spec = new Specifiche("RAM", "16GB");

        // Act
        String result = spec.getNome();

        // Assert
        assertEquals("RAM", result, "Should return the nome set via constructor");
    }

    // ========================================================================
    // Getter Tests: getValore()
    // ========================================================================

    @Test
    @DisplayName("getValore should return null when not set (default constructor)")
    void shouldReturnNullWhenValoreNotSet() {
        // Arrange
        Specifiche spec = new Specifiche();

        // Act
        String result = spec.getValore();

        // Assert
        assertNull(result, "Should return null for default-constructed Specifiche");
    }

    @Test
    @DisplayName("getValore should return valore when set via constructor")
    void shouldReturnValoreWhenSet() {
        // Arrange
        Specifiche spec = new Specifiche("RAM", "16GB");

        // Act
        String result = spec.getValore();

        // Assert
        assertEquals("16GB", result, "Should return the valore set via constructor");
    }

    // ========================================================================
    // Setter Tests: setNome()
    // ========================================================================

    @Test
    @DisplayName("setNome should throw exception when setting null nome")
    void shouldThrowExceptionWhenSettingNullNome() {
        // Arrange
        Specifiche spec = new Specifiche("Original", "Value");

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> spec.setNome(null),
                "Should throw exception when setting null nome");
        assertTrue(exception.getMessage().contains("nome della specifica non può essere null o vuoto"));
        assertEquals("Original", spec.getNome(), "Nome should remain unchanged");
    }

    @Test
    @DisplayName("setNome should throw exception when setting empty nome")
    void shouldThrowExceptionWhenSettingEmptyNome() {
        // Arrange
        Specifiche spec = new Specifiche("Original", "Value");

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> spec.setNome(""),
                "Should throw exception when setting empty nome");
        assertEquals("Original", spec.getNome(), "Nome should remain unchanged");
    }

    @Test
    @DisplayName("setNome should throw exception when setting whitespace nome")
    void shouldThrowExceptionWhenSettingWhitespaceNome() {
        // Arrange
        Specifiche spec = new Specifiche("Original", "Value");

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> spec.setNome("   "),
                "Should throw exception when setting whitespace nome");
    }

    @Test
    @DisplayName("setNome should set valid nome on default-constructed object")
    void shouldSetValidNomeOnDefaultObject() {
        // Arrange
        Specifiche spec = new Specifiche();

        // Act
        spec.setNome("NewKey");

        // Assert
        assertEquals("NewKey", spec.getNome(), "Nome should be set on default object");
    }

    @Test
    @DisplayName("setNome should replace existing nome with new valid nome")
    void shouldReplaceExistingNomeWithNewValidNome() {
        // Arrange
        Specifiche spec = new Specifiche("OldKey", "Value");

        // Act
        spec.setNome("NewKey");

        // Assert
        assertEquals("NewKey", spec.getNome(), "Nome should be replaced");
    }

    // ========================================================================
    // Setter Tests: setValore()
    // ========================================================================

    @Test
    @DisplayName("setValore should throw exception when setting null valore")
    void shouldThrowExceptionWhenSettingNullValore() {
        // Arrange
        Specifiche spec = new Specifiche("Key", "OriginalValue");

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> spec.setValore(null),
                "Should throw exception when setting null valore");
        assertTrue(exception.getMessage().contains("valore della specifica non può essere null o vuoto"));
        assertEquals("OriginalValue", spec.getValore(), "Valore should remain unchanged");
    }

    @Test
    @DisplayName("setValore should throw exception when setting empty valore")
    void shouldThrowExceptionWhenSettingEmptyValore() {
        // Arrange
        Specifiche spec = new Specifiche("Key", "OriginalValue");

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> spec.setValore(""),
                "Should throw exception when setting empty valore");
        assertEquals("OriginalValue", spec.getValore(), "Valore should remain unchanged");
    }

    @Test
    @DisplayName("setValore should throw exception when setting whitespace valore")
    void shouldThrowExceptionWhenSettingWhitespaceValore() {
        // Arrange
        Specifiche spec = new Specifiche("Key", "OriginalValue");

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> spec.setValore("\t\n  "),
                "Should throw exception when setting whitespace valore");
    }

    @Test
    @DisplayName("setValore should set valid valore on default-constructed object")
    void shouldSetValidValoreOnDefaultObject() {
        // Arrange
        Specifiche spec = new Specifiche();

        // Act
        spec.setValore("NewValue");

        // Assert
        assertEquals("NewValue", spec.getValore(), "Valore should be set on default object");
    }

    @Test
    @DisplayName("setValore should replace existing valore with new valid valore")
    void shouldReplaceExistingValoreWithNewValidValore() {
        // Arrange
        Specifiche spec = new Specifiche("Key", "OldValue");

        // Act
        spec.setValore("NewValue");

        // Assert
        assertEquals("NewValue", spec.getValore(), "Valore should be replaced");
    }

    // ========================================================================
    // Integration Tests
    // ========================================================================

    @Test
    @DisplayName("Should handle complete specification lifecycle")
    void shouldHandleCompleteSpecificationLifecycle() {
        // Arrange - Create with valid values
        Specifiche spec = new Specifiche("CPU", "Intel i5");

        // Act & Assert - Verify initial state
        assertEquals("CPU", spec.getNome());
        assertEquals("Intel i5", spec.getValore());

        // Act - Update nome
        spec.setNome("Processor");
        assertEquals("Processor", spec.getNome());
        assertEquals("Intel i5", spec.getValore(), "Valore should not change");

        // Act - Update valore
        spec.setValore("Intel i7");
        assertEquals("Processor", spec.getNome(), "Nome should not change");
        assertEquals("Intel i7", spec.getValore());
    }

    @Test
    @DisplayName("Should handle special characters in nome and valore")
    void shouldHandleSpecialCharacters() {
        // Arrange & Act
        Specifiche spec = new Specifiche(
                "Display Size (diagonal)",
                "15.6\" Full HD (1920x1080)");

        // Assert
        assertEquals("Display Size (diagonal)", spec.getNome());
        assertEquals("15.6\" Full HD (1920x1080)", spec.getValore());
    }
}
