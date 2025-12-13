package services;

import model.beans.Utente;
import model.dao.UtenteDAO;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class UtenteServiceTest {

    @Mock
    private UtenteDAO utenteDAO;

    @InjectMocks
    private UtenteService userService;

    // =================================================================================================
    // Default Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should instantiate service via default constructor")
    void shouldInitializeSuccessfullyWhenDefaultConstructorIsCalled() throws SQLException {
        // Act
        UtenteService service = new UtenteService();

        // Assert
        assertNotNull(service);
    }

    // =================================================================================================
    // Constructor (UtenteDAO) Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should instantiate service when UtenteDAO is non-null")
    void shouldInitializeSuccessfullyWhenDaoIsNotNull() {
        // Act
        assertNotNull(userService);
    }

    @Test
    @DisplayName("TF2: Should throw exception when UtenteDAO is null")
    void shouldThrowIllegalArgumentExceptionWhenDaoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new UtenteService(null));
        assertTrue(exception.getMessage().contains("UtenteDAO cannot be null"));
    }

    // =================================================================================================
    // getUtenteById Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should return Utente when id is positive and found")
    void shouldReturnUtenteWhenIdIsPositiveAndFound() throws SQLException {
        // Arrange
        int validUserId = 1;
        Utente expectedUser = new Utente();

        when(utenteDAO.getUtenteById(validUserId)).thenReturn(expectedUser);

        // Act
        Utente user = userService.getUtenteById(validUserId);

        // Assert
        assertAll(
                () -> assertNotNull(user),
                () -> assertEquals(expectedUser, user));

        verify(utenteDAO).getUtenteById(validUserId);
    }

    @Test
    @DisplayName("TF2: Should return null when id is positive and not found")
    void shouldReturnNullWhenIdIsPositiveAndNotFound() throws SQLException {
        // Arrange
        int notFoundUserId = 99;
        when(utenteDAO.getUtenteById(notFoundUserId)).thenReturn(null);

        // Act
        Utente user = userService.getUtenteById(notFoundUserId);

        // Assert
        assertNull(user);

        verify(utenteDAO).getUtenteById(notFoundUserId);
    }

    @Test
    @DisplayName("TF3: Should throw SQLException when DAO fails")
    void shouldThrowSqlExceptionWhenDaoFails() throws SQLException {
        // Arrange
        int validUserId = 1;
        when(utenteDAO.getUtenteById(validUserId)).thenThrow(new SQLException("Database error"));

        // Act & Assert
        assertThrows(
                SQLException.class,
                () -> userService.getUtenteById(validUserId));

        verify(utenteDAO).getUtenteById(validUserId);
    }

    @ParameterizedTest
    @DisplayName("TF4, TF5: Should throw IllegalArgumentException when id is invalid")
    @CsvSource({ "0", "-1", "-100" })
    void shouldThrowIllegalArgumentExceptionWhenIdIsInvalid(int invalidId) {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> userService.getUtenteById(invalidId));
        assertTrue(exception.getMessage().contains("ID must be positive"));
    }
}
