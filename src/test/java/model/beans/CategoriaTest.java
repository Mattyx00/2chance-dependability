package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

class CategoriaTest {

    // ========================================================================
    // 2.1 Constructor: Categoria()
    // ========================================================================

    @Test
    @DisplayName("shouldCreateCategoriaWithNullNameWhenUsingDefaultConstructor")
    void shouldCreateCategoriaWithNullNameWhenUsingDefaultConstructor() {
        // Act
        Categoria category = new Categoria();

        // Assert
        assertNotNull(category);
        assertNull(category.getNomeCategoria(), "Nome category should be null initially");
    }

    // ========================================================================
    // 2.2 Constructor: Categoria(String nomeCategoria)
    // ========================================================================

    @ParameterizedTest
    @NullSource
    @ValueSource(strings = { "", "   ", "\t", "\n" })
    @DisplayName("shouldThrowIllegalArgumentExceptionWhenNomeCategoriaIsInvalidInConstructor")
    void shouldThrowIllegalArgumentExceptionWhenNomeCategoriaIsInvalidInConstructor(String nameCategory) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new Categoria(nameCategory));
        assertEquals("Il nome della categoria non può essere null o vuoto", exception.getMessage());
    }

    @ParameterizedTest
    @ValueSource(strings = { "A", "Electronics", "Very Long Category Name With Many Words" })
    @DisplayName("shouldCreateCategoriaWhenNomeCategoriaIsValid")
    void shouldCreateCategoriaWhenNomeCategoriaIsValid(String nameCategory) {
        // Act
        Categoria category = new Categoria(nameCategory);

        // Assert
        assertNotNull(category);
        assertEquals(nameCategory, category.getNomeCategoria());
    }

    // ========================================================================
    // 2.3 Method: String getNomeCategoria()
    // ========================================================================

    @Test
    @DisplayName("shouldReturnNullWhenNomeCategoriaNotYetSet")
    void shouldReturnNullWhenNomeCategoriaNotYetSet() {
        // Arrange
        Categoria category = new Categoria();

        // Act
        String nameCategory = category.getNomeCategoria();

        // Assert
        assertNull(nameCategory);
    }

    @Test
    @DisplayName("shouldReturnNomeCategoriaWhenSet")
    void shouldReturnNomeCategoriaWhenSet() {
        // Arrange
        String expectedName = "Books";
        Categoria category = new Categoria(expectedName);

        // Act
        String nameCategory = category.getNomeCategoria();

        // Assert
        assertEquals(expectedName, nameCategory);
    }

    // ========================================================================
    // 2.4 Method: void setNomeCategoria(String nomeCategoria)
    // ========================================================================

    @ParameterizedTest
    @NullSource
    @ValueSource(strings = { "", "   ", "\t", "\n" })
    @DisplayName("shouldThrowIllegalArgumentExceptionWhenSettingInvalidName")
    void shouldThrowIllegalArgumentExceptionWhenSettingInvalidName(String invalidName) {
        // Arrange
        String originalCategoryName = "Original";
        Categoria category = new Categoria(originalCategoryName);

        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> category.setNomeCategoria(invalidName));
        assertEquals("Il nome della categoria non può essere null o vuoto", exception.getMessage());
        assertEquals(originalCategoryName, category.getNomeCategoria(), "Name should remain unchanged");
    }

    @Test
    @DisplayName("shouldSetValidNameOnDefaultConstructedObject")
    void shouldSetValidNameOnDefaultConstructedObject() {
        // Arrange
        Categoria category = new Categoria();
        String newCategoryName = "NewCategory";

        // Act
        category.setNomeCategoria(newCategoryName);

        // Assert
        assertEquals(newCategoryName, category.getNomeCategoria());
    }

    @Test
    @DisplayName("shouldReplaceExistingNameWithNewValidName")
    void shouldReplaceExistingNameWithNewValidName() {
        // Arrange
        Categoria category = new Categoria("OldCategory");
        String newCategoryName = "NewCategory";

        // Act
        category.setNomeCategoria(newCategoryName);

        // Assert
        assertEquals(newCategoryName, category.getNomeCategoria());
    }
}
