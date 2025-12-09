package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.NullAndEmptySource;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

class SpecificheTest {

    // ================================================================================
    // Constructor: Specifiche(String nome, String valore)
    // ================================================================================

    /**
     * Test Frame F1: Valid Construction
     * Inputs: nome="Materiale", valore="Legno"
     * Expected: Object created successfully. getNome() returns "Materiale",
     * getValore() returns "Legno".
     */
    @Test
    @DisplayName("shouldConstructorCreateObjectWhenInputsAreValid")
    void shouldConstructorCreateObjectWhenInputsAreValid() {
        // Arrange
        String nome = "Materiale";
        String valore = "Legno";

        // Act
        Specifiche specifiche = new Specifiche(nome, valore);

        // Assert
        assertAll("Verify Object State",
                () -> assertEquals(nome, specifiche.getNome(), "Nome must match the input"),
                () -> assertEquals(valore, specifiche.getValore(), "Valore must match the input"));
    }

    /**
     * Test Frames F2, F3, F4: Invalid Construction - Name is Null, Empty, or Blank
     * Inputs: nome=null/"/" ", valore="Legno"
     * Expected: IllegalArgumentException thrown ("Il nome della specifica non può
     * essere null o vuoto").
     */
    @ParameterizedTest
    @NullAndEmptySource
    @DisplayName("shouldConstructorThrowExceptionWhenNomeIsInvalid")
    void shouldConstructorThrowExceptionWhenNomeIsInvalid(String invalidName) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Specifiche(invalidName, "Legno"));
        assertEquals("Il nome della specifica non può essere null o vuoto", exception.getMessage());
    }

    /**
     * Test Frames F5, F6, F7: Invalid Construction - Value is Null, Empty, or Blank
     * Inputs: nome="Materiale", valore=null/"/" "
     * Expected: IllegalArgumentException thrown ("Il valore della specifica non può
     * essere null o vuoto").
     */
    @ParameterizedTest
    @NullAndEmptySource
    @DisplayName("shouldConstructorThrowExceptionWhenValoreIsInvalid")
    void shouldConstructorThrowExceptionWhenValoreIsInvalid(String invalidValue) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Specifiche("Materiale", invalidValue));
        assertEquals("Il valore della specifica non può essere null o vuoto", exception.getMessage());
    }

    // ================================================================================
    // Constructor: Specifiche()
    // ================================================================================

    /**
     * Test Frame F8: Default Construction
     * Inputs: None
     * Expected: Object created successfully. Fields nome and valore are null.
     */
    @Test
    @DisplayName("shouldCreateEmptyObjectUsingDefaultConstructor")
    void shouldCreateEmptyObjectUsingDefaultConstructor() {
        // Act
        Specifiche specifiche = new Specifiche();

        // Assert
        assertAll("Verify Default State",
                () -> assertNull(specifiche.getNome(), "Nome should be null"),
                () -> assertNull(specifiche.getValore(), "Valore should be null"));
    }

    // ================================================================================
    // Method: setNome(String nome)
    // ================================================================================

    /**
     * Test Frame F9: Set Valid Name
     * Inputs: nome="Dimensione"
     * Expected: Field nome is updated to "Dimensione".
     */
    @Test
    @DisplayName("shouldSetNomeWhenInputIsValid")
    void shouldSetNomeWhenInputIsValid() {
        // Arrange
        Specifiche specifications = new Specifiche();
        String validName = "Dimensione";

        // Act
        specifications.setNome(validName);

        // Assert
        assertEquals(validName, specifications.getNome());
    }

    /**
     * Test Frames F10, F11, F12: Set Invalid Name
     * Inputs: nome=null, "", " "
     * Expected: IllegalArgumentException thrown.
     */
    @ParameterizedTest
    @NullAndEmptySource
    @DisplayName("shouldSetNomeThrowExceptionWhenInputIsInvalid")
    void shouldSetNomeThrowExceptionWhenInputIsInvalid(String invalidName) {
        // Arrange
        Specifiche specifications = new Specifiche();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> specifications.setNome(invalidName));
        assertEquals("Il nome della specifica non può essere null o vuoto", exception.getMessage());
    }

    // ================================================================================
    // Method: setValore(String valore)
    // ================================================================================

    /**
     * Test Frame F13: Set Valid Value
     * Inputs: valore="Grande"
     * Expected: Field valore is updated to "Grande".
     */
    @Test
    @DisplayName("shouldSetValoreWhenInputIsValid")
    void shouldSetValoreWhenInputIsValid() {
        // Arrange
        Specifiche specifications = new Specifiche();
        String validValue = "Grande";

        // Act
        specifications.setValore(validValue);

        // Assert
        assertEquals(validValue, specifications.getValore());
    }

    /**
     * Test Frames F14, F15, F16: Set Invalid Value
     * Inputs: valore=null, "", " "
     * Expected: IllegalArgumentException thrown.
     */
    @ParameterizedTest
    @NullAndEmptySource
    @DisplayName("shouldSetValoreThrowExceptionWhenInputIsInvalid")
    void shouldSetValoreThrowExceptionWhenInputIsInvalid(String invalidValue) {
        // Arrange
        Specifiche specifications = new Specifiche();

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> specifications.setValore(invalidValue));
        assertEquals("Il valore della specifica non può essere null o vuoto", exception.getMessage());
    }
}
